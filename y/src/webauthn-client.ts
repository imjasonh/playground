// Inline JS shipped to the admin login and passkey-manage pages.
// Hand-rolled converter between WebAuthn's base64url JSON and the
// ArrayBuffer-typed `navigator.credentials` API. ~60 lines minified.

export const WEBAUTHN_CLIENT_JS = `
const b64u = {
  dec: s => {
    s = s.replace(/-/g,'+').replace(/_/g,'/');
    while (s.length % 4) s += '=';
    return Uint8Array.from(atob(s), c => c.charCodeAt(0)).buffer;
  },
  enc: buf => btoa(String.fromCharCode(...new Uint8Array(buf)))
    .replace(/\\+/g,'-').replace(/\\//g,'_').replace(/=+$/,''),
};

async function postJSON(url, body) {
  const r = await fetch(url, {
    method: 'POST',
    headers: body ? {'content-type': 'application/json'} : {},
    body: body ? JSON.stringify(body) : undefined,
    credentials: 'same-origin',
  });
  if (!r.ok) throw new Error('HTTP ' + r.status + ': ' + (await r.text()));
  const ct = r.headers.get('content-type') || '';
  return ct.includes('application/json') ? r.json() : null;
}

async function pkRegister(label) {
  const opts = await postJSON('/admin/passkeys/register/options');
  opts.challenge = b64u.dec(opts.challenge);
  opts.user.id = b64u.dec(opts.user.id);
  if (opts.excludeCredentials) {
    opts.excludeCredentials = opts.excludeCredentials.map(c => ({...c, id: b64u.dec(c.id)}));
  }
  const cred = await navigator.credentials.create({ publicKey: opts });
  const resp = {
    id: cred.id,
    rawId: b64u.enc(cred.rawId),
    type: cred.type,
    response: {
      attestationObject: b64u.enc(cred.response.attestationObject),
      clientDataJSON: b64u.enc(cred.response.clientDataJSON),
      transports: cred.response.getTransports ? cred.response.getTransports() : [],
    },
    clientExtensionResults: cred.getClientExtensionResults ? cred.getClientExtensionResults() : {},
    authenticatorAttachment: cred.authenticatorAttachment || null,
  };
  await postJSON('/admin/passkeys/register/verify', { label, response: resp });
  location.reload();
}

async function pkLogin() {
  const opts = await postJSON('/admin/login/passkey/options');
  opts.challenge = b64u.dec(opts.challenge);
  if (opts.allowCredentials) {
    opts.allowCredentials = opts.allowCredentials.map(c => ({...c, id: b64u.dec(c.id)}));
  }
  const cred = await navigator.credentials.get({ publicKey: opts });
  const resp = {
    id: cred.id,
    rawId: b64u.enc(cred.rawId),
    type: cred.type,
    response: {
      authenticatorData: b64u.enc(cred.response.authenticatorData),
      clientDataJSON: b64u.enc(cred.response.clientDataJSON),
      signature: b64u.enc(cred.response.signature),
      userHandle: cred.response.userHandle ? b64u.enc(cred.response.userHandle) : null,
    },
    clientExtensionResults: cred.getClientExtensionResults ? cred.getClientExtensionResults() : {},
    authenticatorAttachment: cred.authenticatorAttachment || null,
  };
  await postJSON('/admin/login/passkey/verify', resp);
  location.href = '/admin';
}

window.pkRegister = pkRegister;
window.pkLogin = pkLogin;
`;
