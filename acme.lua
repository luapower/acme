
--ACME v2 HTTP-01 protocol. WORK IN PROGRESS!
--Written by fffonion. BSD License.
--Ripped from https://github.com/fffonion/lua-resty-acme/blob/master/lib/resty/acme/client.lua
--Modified by Cosmin Apreutesei.

local http = require'http'
local cjson = require'cjson'
local openssl = 'openssl'
local b64 = require'base64'
local sha2 = require'sha2'
local json = cjson.new()

-- some implemntations like ZeroSSL doesn't like / to be escaped
json.encode_escape_forward_slash(false)

-- https://tools.ietf.org/html/rfc8555 Page 10
-- Binary fields in the JSON objects used by acme are encoded using
-- base64url encoding described in Section 5 of [RFC4648] according to
-- the profile specified in JSON Web Signature in Section 2 of
-- [RFC7515].  This encoding uses a URL safe character set.  Trailing
-- '=' characters MUST be stripped.  Encoded values that include
-- trailing '=' characters MUST be rejected as improperly encoded.
local function encode_base64url(s)
	return b64.encode(s):gsub('/', '_'):gsub('+', '-'):gsub('=*$', '')
end
local function decode_base64url(s)
	return b64.decode(s):gsub('_', '/'):gsub('-', '+'):gsub('=*$', '')
end

-- https://tools.ietf.org/html/rfc7638
local function thumbprint(pkey)
	local params = assert(pkey:get_parameters())
	local jwk_ordered = string.format('{"e":"%s","kty":"RSA","n":"%s"}',
		encode_base64url(params.e:to_binary()),
		encode_base64url(params.n:to_binary())
	)
	local hash = sha2.sha256(jwk_ordered)
	return encode_base64url(hash)
end

local function create_csr(domain_pkey, ...)
	local subject = openssl.name.new()
	local assert(subject:add('CN', (...)))
	-- add subject name to altname as well, some implementaions
	-- like ZeroSSL requires that
	local alt
	for i = 1, select('#',...) do
		local domain = select(i, ...)
		alt = alt or assert(openssl.altname.new())
		assert(alt:add("DNS", domain))
	end
	local csr = openssl.csr.new()
	csr:set_subject_name(subject)
	if alt then
		csr:set_subject_alt_name(alt)
	end
	csr:set_pubkey(domain_pkey)
	csr:sign(domain_pkey)
	return csr:tostring'DER'
end

local pem_cert_header = '-----BEGIN CERTIFICATE-----'
local pem_cert_footer = '-----END CERTIFICATE-----'
local function check_chain_root_issuer(chain_pem, issuer_name)
	-- find the last pem cert block in the chain file.
	local pos = 0
	local pem
	while true do
		local newpos = chain_pem:find(pem_cert_header, pos + 1, true)
		if not newpos then
			local endpos = chain_pem:find(pem_cert_footer, pos+1, true)
			if endpos then
				pem = chain_pem:sub(pos, endpos+#pem_cert_footer-1)
			end
			break
		end
		pos = newpos
	end
	assert(pem)
	local cert = openssl.x509.new(pem)
	local name = cert:get_issuer_name()
	local cn = name:find'CN'
	assert(cn and cn.blob == issuer_name)
end

local function ch_key(challenge)
	return challenge .. '#http-01'
end

function acme:register_challenge(challenge, resonse, _--[[domains]])
	return self.storage:set(ch_key(challenge), resonse, 3600)
end

function acme:cleanup_challenge(challenge, _--[[domains]])
	return self.storage:delete(ch_key(challenge))
end

function acme:serve_challenge(uri)
	local captures, err =
		ngx.re.match(ngx.var.request_uri, [[\.well-known/]] .. 'acme-challenge/(.+)", "jo")
	local token = captures[1]
	log(ngx.DEBUG, "token is ", token)
	local value, err = self.storage:get(ch_key(token))
	ngx.say(value)
end

local wait_backoff_series = {1, 1, 2, 3, 5, 8, 13, 21}

local TEST_TRY_NONCE_INFINITELY = not not os.getenv('TEST_TRY_NONCE_INFINITELY')

local acme = {}
acme.api_uri = 'https://acme-v02.api.letsencrypt.org/directory' --ACME v2 API endpoint
acme.account_email = nil -- the account email to register
acme.account_key = nil -- the account key in PEM format text
acme.account_kid = nil -- the account kid (as an URL)
acme.eab_kid = nil -- external account binding key id
acme.eab_hmac_key = nil -- external account binding hmac key, base64url encoded
acme.eab_handler = nil -- external account registering handler
acme.storage_adapter = 'shm' -- storage for challenge
acme.preferred_chain = nil -- select preferred root CA issuer's Common Name if appliable
acme.challenge_start_callback = nil -- callback function that allows to wait before signaling ACME server to validate

function acme.new(t)
	local self = setmetatable(t or {}, {__index = acme})
	self.eab_required = false --CA requires external account binding or not
	self.eab_hmac_key = decode_base64url(self.eab_hmac_key)
	self.challenge_handlers = {}
	if self.account_key then
		self.account_pkey = openssl.pkey.new(self.account_key)
		self.account_thumbprint = thumbprint(self.account_pkey)
	end
	return self
end

function acme:init()

	local httpc = new_httpc()

	local res, err = httpc:request_uri(self.conf.api_uri)
	if err then
		return 'acme directory request failed: ' .. err
	end

	if res and res.status == 200 and res.headers['content-type'] and
			res.headers['content-type']:match'application/json'
	 then
		local directory = json.decode(res.body)
		if not directory then
			return 'acme directory listing resonse malformed'
		end
		self.directory = directory
	else
		local status = res and res.status
		local content_type = res and res.headers and res.headers['content-type']
		return string.format('acme directory listing failed: status code %s, content-type %s',
						status, content_type)
	end

	if not self.directory['newNonce'] or
			not self.directory['newAccount'] or
			not self.directory['newOrder'] or
			not self.directory['revokeCert'] then
		return 'acme directory endpoint is missing at least one of '..
						'newNonce, newAccount, newOrder or revokeCert endpoint'
	end

	if self.directory['meta'] and
			self.directory['meta']['externalAccountRequired'] then

		self.eab_required = true

		if not self.eab_handler and
			(not self.eab_kid or not self.eab_hmac_key) then

			-- try to load a predefined eab handler
			local website = self.directory['meta'] and self.directory['meta']['website']
			if website then
				-- load the module based on website metadata
				website = ngx.re.sub(website, [=[^https?://([^/]+).*$]=], '$1'):gsub('%.', '-')
				local pok, eab_handler_module = pcall(require, 'resty.acme.eab.' .. website)
				if pok and eab_handler_module and eab_handler_module.handle then
					log(ngx_INFO, 'loaded EAB module ', 'resty.acme.eab.' .. website)
					self.eab_handler = eab_handler_module.handle
					return
				end
			end

			return 'CA requires external account binding, either define a eab_handler to automatically '..
						'register account, or define eab_kid and eab_hmac_key for existing account'
		end
	end

	return nil
end

--- Enclose the provided payload in JWS
--
-- @param url       ACME service URL
-- @param payload   (json) data which will be wrapped in JWS
-- @param nonce     nonce to be used in JWS, if not provided new nonce will be requested
function acme:jws(url, payload, nonce)
	if not self.account_pkey then
		return nil, 'account key does not specified'
	end

	if not url then
		return nil, 'url is not defined'
	end

	if not nonce then
		local err
		nonce, err = self:new_nonce()
		if err then
			return nil, 'can\'t get new nonce from acme server: ' .. err
		end
	end

	local jws = {
		protected = {
			alg = 'RS256',
			nonce = nonce,
			url = url
		},
		payload = payload
	}

	-- TODO: much better handling
	if payload and payload.contact then
		local params, err = self.account_pkey:get_parameters()
		if not params then
			return nil, 'can\'t get parameters from account key: ' .. (err or 'nil')
		end

		jws.protected.jwk = {
			e = encode_base64url(params.e:to_binary()),
			kty = 'RSA',
			n = encode_base64url(params.n:to_binary())
		}

		if self.eab_required then
			local eab_jws = {
				protected = {
					alg = 'HS256',
					kid = self.eab_kid,
					url = url
				},
				payload = jws.protected.jwk,
			}

			log(ngx_DEBUG, 'eab jws payload: ', json.encode(eab_jws))

			eab_jws.protected = encode_base64url(json.encode(eab_jws.protected))
			eab_jws.payload = encode_base64url(json.encode(eab_jws.payload))
			local hmac = openssl.hmac.new(self.eab_hmac_key, 'SHA256')
			local sig = hmac:final(eab_jws.protected .. '.' .. eab_jws.payload)
			eab_jws.signature = encode_base64url(sig)

			payload['externalAccountBinding'] = eab_jws
		end
	elseif not self.account_kid then
		return nil, 'account_kid is not defined, provide via config or create account first'
	else
		jws.protected.kid = self.account_kid
	end

	log(ngx_DEBUG, 'jws payload: ', json.encode(jws))

	jws.protected = encode_base64url(json.encode(jws.protected))
	-- if payload is not set, we are doing a POST-as-GET (https://tools.ietf.org/html/rfc8555#section-6.3)
	-- set it to empty string
	jws.payload = payload and encode_base64url(json.encode(payload)) or ''
	local digest = openssl.digest.new('SHA256')
	digest:update(jws.protected .. '.' .. jws.payload)
	jws.signature = encode_base64url(self.account_pkey:sign(digest))

	return json.encode(jws)
end

function acme:post(url, payload, headers, nonce)
	local httpc = new_httpc()
	if not headers then
		headers = {
			['content-type'] = 'application/jose+json'
		}
	elseif not headers['content-type'] then
		headers['content-type'] = 'application/jose+json'
	end

	local jws, err = self:jws(url, payload, nonce)
	if not jws then
		return nil, nil, err
	end

	local res, err = httpc:request_uri(url,
		{
			method = 'POST',
			body = jws,
			headers = headers
		}
	)

	if err then
		return nil, nil, err
	end
	log(ngx_DEBUG, 'acme request: ', url, ' resonse: ', res.body)

	local body
	if res.headers['Content-Type']:sub(1, 16) == 'application/json' then
		body = json.decode(res.body)
	elseif res.headers['Content-Type']:sub(1, 24) == 'application/problem+json' then
		body = json.decode(res.body)
		if body.type == 'urn:ietf:params:acme:error:badNonce' and res.headers['Replay-Nonce'] then
			if not nonce then
				log(ngx_WARN, 'bad nonce: recoverable error, retrying')
				return self:post(url, payload, headers, res.headers['Replay-Nonce'])
			elseif not TEST_TRY_NONCE_INFINITELY then
				return nil, nil, 'bad nonce: failed again, bailing out'
			end
		else
			return nil, nil, body.detail or body.type
		end
	else
		body = res.body
	end

	return body, res.headers, err
end

function acme:new_account()
	if self.account_kid then
		return self.account_kid, nil
	end

	local payload = {
		termsOfServiceAgreed = true,
	}

	if self.conf.account_email then
		payload['contact'] = {
			'mailto:' .. self.conf.account_email,
		}
	end

	if self.eab_required then
		if not self.eab_handler then
			return nil, 'eab_handler undefined while EAB is required by CA'
		end
		local eab_kid, eab_hmac_key, err = self.eab_handler(self.conf.account_email)
		if err then
			return nil, 'eab_handler returned an error: ' .. err
		end
		self.eab_kid = eab_kid
		self.eab_hmac_key = decode_base64url(eab_hmac_key)
	end

	local _, headers, err = self:post(self.directory['newAccount'], payload)

	if err then
		return nil, 'failed to create account: ' .. err
	end

	self.account_kid = headers['location']

	return self.account_kid, nil
end

function acme:new_nonce()
	local httpc = new_httpc()
	local res, err = httpc:request_uri(self.directory['newNonce'],
		{
			method = 'HEAD'
		}
	)

	if res and res.headers then
		-- TODO: Expect status code 204
		-- TODO: Expect Cache-Control: no-store
		-- TODO: Expect content size 0
		return res.headers['replay-nonce']
	else
		return nil, 'failed to fetch new nonce: ' .. err
	end
end

function acme:new_order(...)
	local domains = {...}
	if domains.n == 0 then
		return nil, nil, 'at least one domains should be provided'
	end

	local identifiers = {}
	for i, domain in ipairs(domains) do
		identifiers[i] = {
			type = 'dns',
			value = domain
		}
	end

	local body, headers, err = self:post(self.directory['newOrder'],
		{
			identifiers = identifiers,
		}
	)

	if err then
		return nil, nil, err
	end

	return body, headers, nil
end

local function watch_order_status(self, order_url, target)
	local order_status, err
	for _, t in pairs(wait_backoff_series) do
		ngx.sleep(t)
		-- POST-as-GET request with empty payload
		order_status, _, err = self:post(order_url)
		log(ngx_DEBUG, 'check order: ', json.encode(order_status), ' err: ', err)
		if order_status then
			if order_status.status == target then
				break
			elseif order_status.status == 'invalid' then
				local errors = {}
				for _, authz in ipairs(order_status.authorizations) do
					local authz_status, _, err = self:post(authz)
					if err then
						log(ngx_WARN, 'error fetching authorization final status:', err)
					else
						for _, c in ipairs(authz_status.challenges) do
							log(ngx_DEBUG, 'authorization status: ', json.encode(c))
							local err_msg = c['type'] .. ': ' .. c['status']
							if c['error'] and c['error']['detail'] then
								err_msg = err_msg .. ': ' .. c['error']['detail']
							end
							errors[#errors+1] = err_msg
						end
					end
				end
				return nil, 'challenge invalid: ' .. table.concat(errors, '; ')
			end
		end
	end

	if not order_status then
		return nil, 'could not get order status'
	end

	if order_status.status ~= target then
		return nil, 'failed to wait for order status, got ' .. (order_status.status or 'nil')
	end

	return order_status
end


local rel_alternate_pattern = '<(.+)>;%s*rel='alternate''
local function parse_alternate_link(headers)
	local link_header = headers['Link']
	if type(link_header) == 'string' then
		return link_header:match(rel_alternate_pattern)
	elseif link_header then
		for _, link in pairs(link_header) do
			local m = link:match(rel_alternate_pattern)
			if m then
				return m
			end
		end
	end
end

function acme:finalize(finalize_url, order_url, csr)
	local payload = {
		csr = encode_base64url(csr)
	}

	local res, headers, err = self:post(finalize_url, payload)

	if err then
		return nil, 'failed to send finalize request: ' .. err
	end

	if not headers['content-type'] == 'application/pem-certificate-chain' then
		return nil, 'wrong content type'
	end

	-- Wait until the order is valid: ready to download
	if not res.certificate and res.status and res.status == 'valid' then
		log(ngx_DEBUG, json.encode(res))
		return nil, 'no certificate object returned ' .. (res.detail or '')
	end

	local order_status, err = watch_order_status(self, order_url, 'valid')
	if not order_status or not order_status.certificate then
		return nil, 'error checking finalize: ' .. err
	end

	-- POST-as-GET request with empty payload
	local body, headers, err = self:post(order_status.certificate)
	if err then
		return nil, 'failed to fetch certificate: ' .. err
	end

	local preferred_chain = self.conf.preferred_chain
	if not preferred_chain then
		return body
	end

	local ok, err = util.check_chain_root_issuer(body, preferred_chain)
	if not ok then
		log(ngx_DEBUG, 'configured preferred chain issuer CN \'', preferred_chain, '\' not found ',
										'in default chain, downloading alternate chain: ', err)
		local alternate_link = parse_alternate_link(headers)
		if not alternate_link then
			log(ngx_WARN, 'failed to fetch alternate chain because no alternate link is found, ',
										'fallback to default chain')
		else
			local body_alternate, _, err = self:post(alternate_link)

			if err then
				log(ngx_WARN, 'failed to fetch alternate chain, fallback to default: ', err)
			else
				local ok, err = util.check_chain_root_issuer(body_alternate, preferred_chain)
				if ok then
					log(ngx_DEBUG, 'alternate chain is selected')
					return body_alternate
				end
				log(ngx_WARN, 'configured preferred chain issuer CN \'', preferred_chain, '\' also not found ',
											'in alternate chain, fallback to default chain: ', err)
			end
		end
	end

	return body
end

-- create certificate workflow, used in new cert or renewal
function acme:order_certificate(domain_key, ...)
	-- create new-order request
	local order_body, order_headers, err = self:new_order(...)
	if err then
		return nil, 'failed to create new order: ' .. err
	end

	log(ngx_DEBUG, 'new order: ', json.encode(order_body))

	-- setup challenges
	local finalize_url = order_body.finalize
	local order_url = order_headers['location']
	local authzs = order_body.authorizations
	local registered_challenges = {}
	local registered_challenge_count = 0
	local has_valid_challenge = false

	for _, authz in ipairs(authzs) do
		-- POST-as-GET request with empty payload
		local challenges, _, err = self:post(authz)
		if err then
			return nil, 'failed to fetch authz: ' .. err
		end

		if not challenges.challenges then
			log(ngx_WARN, 'fetching challenges returns an error: ', err)
			goto nextchallenge
		end
		for _, challenge in ipairs(challenges.challenges) do
			local typ = challenge.type
			if challenge.status ~= 'pending' then
				if challenge.status == 'valid' then
					has_valid_challenge = true
				end
				log(ngx_DEBUG, 'challenge ', typ, ': ', challenge.token, ' is ', challenge.status, ', skipping')
			elseif self.challenge_handlers[typ] then
				local err = self:register_challenge(
					challenge.token,
					challenge.token .. '.' .. self.account_thumbprint,
					{...}
				)
				if err then
					return nil, 'error registering challenge: ' .. err
				end
				registered_challenges[registered_challenge_count + 1] = challenge.token
				registered_challenge_count = registered_challenge_count + 1
				log(ngx_DEBUG, 'register challenge ', typ, ': ', challenge.token)
				if self.conf.challenge_start_callback then
					while not self.conf.challenge_start_callback(typ, challenge.token) do
						ngx.sleep(1)
					end
				end
				-- signal server to start challenge check
				-- needs to be empty json body rather than empty string
				-- https://tools.ietf.org/html/rfc8555#section-7.5.1
				local _, _, err = self:post(challenge.url, {})
				if err then
					return nil, 'error start challenge check: ' .. err
				end
			end
		end
::nextchallenge::
	end

	if registered_challenge_count == 0 and not has_valid_challenge then
		return nil, 'no challenge is registered and no challenge is valid'
	end

	-- Wait until the order is ready
	local order_status, err = watch_order_status(self, order_url, 'ready')
	if not order_status then
		return nil, 'error checking challenge: ' .. err
	end

	local domain_pkey, err = openssl.pkey.new(domain_key)
	if err then
		return nil, 'failed to load domain pkey: ' .. err
	end

	local csr, err = util.create_csr(domain_pkey, ...)
	if err then
		return nil, 'failed to create csr: ' .. err
	end

	local cert, err = self:finalize(finalize_url, order_url, csr)
	if err then
		return nil, err
	end

	log(ngx_DEBUG, 'order is completed: ', order_url)

	for _, token in ipairs(registered_challenges) do
		for _, ch in pairs(self.challenge_handlers) do
			ch:cleanup_challenge(token, {...})
		end
	end

	return cert, nil
end

return acme
