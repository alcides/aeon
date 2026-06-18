# `Http`: typed bindings for the `requests` library

The [`requests`](https://requests.readthedocs.io/) library is a pleasure to use
and a reliable source of production incidents — almost always in the same three
ways. `Http.ae` wraps it so each of those failure modes becomes a compile-time
error instead of a runtime surprise. For the general mechanics of writing such a
binding, see [Writing FFI bindings for a Python package](ffi); for two more
worked examples in the same spirit, see
[`os` and `subprocess`](os-subprocess).

- Source: [`libraries/Http.ae`](https://github.com/alcides/aeon/blob/master/libraries/Http.ae)
- Example: [`examples/imports/http_example.ae`](https://github.com/alcides/aeon/blob/master/examples/imports/http_example.ae)

---

## 1. Requests can't hang forever

A `requests` call with no `timeout` blocks indefinitely if the peer never
answers — the classic "the whole service froze" outage. Every entry point in
`Http.ae` *requires* a strictly positive timeout (in seconds), and there is no
timeout-less overload to reach for by accident:

```aeon
def get (url: {u:String | u != ""}) (timeout: {t:Float | t > 0.0}) : Response :=
    native "requests.get(url, timeout=timeout)"
```

A non-positive timeout — which `requests` interprets as "fail immediately" (`0`)
or "wait forever" (`None`) — is rejected:

```aeon
def bad : Response := Http.get "http://example.com" 0.0
```

```
>>> Type error: Failed to prove (vt == 0.0) ... t > 0.0
```

The same precondition rules out the empty URL that would otherwise raise
`MissingSchema`.

## 2. Status codes you can't ignore

`requests` does not raise on a 4xx or 5xx; it is easy to parse the body of a
request that never succeeded. The status is reflected into an **uninterpreted
measure**, and `isSuccess` is tied to it so a test refines the response in the
`then` branch:

```aeon
def status : (r: Response) -> Int := uninterpreted

def isSuccess (r: Response) : {b:Bool | b = (status r >= 200 && status r < 300)} :=
    native "(200 <= r.status_code) and (r.status_code < 300)"
```

```aeon
def fetchTitle (url: {u:String | u != ""}) : String :=
    let r : Response := Http.get url 5.0 in
    if Http.isSuccess r then
        Http.body r            # only read the body on a 2xx
    else
        "request failed";
```

When you'd rather treat any error status as fatal, `raiseForStatus` raises
`HTTPError` on a 4xx/5xx and carries the postcondition `status r < 400` — so the
rest of your code can trust the request succeeded, at the type level:

```aeon
def raiseForStatus (r: Response) : {x:Response | status x < 400} :=
    native "(r.raise_for_status(), r)[1]"
```

## 3. JSON bodies are parsed, not assumed

`response.json()` raises `JSONDecodeError` on a non-JSON body. `bodyJson` returns
a [`Json`](https://github.com/alcides/aeon/blob/master/libraries/Json.ae) value,
which you then interrogate with the runtime-typed `Json` coercions (`isObject`,
`asString`, …) rather than assuming a dict:

```aeon
def fetchJson (url: {u:String | u != ""}) : Json :=
    let r : Response := Http.raiseForStatus (Http.get url 5.0) in
    Http.bodyJson r;
```

## Quick reference

| Function | Notes |
|---|---|
| `get url timeout` | GET; `url != ""`, `timeout > 0.0` |
| `getWithHeaders url headers timeout` | headers as a `Map String String` |
| `post url body timeout` | POST a raw string body |
| `postJson url payload timeout` | POST a `Json` payload (sets `Content-Type`) |
| `put url body timeout` | PUT a raw string body |
| `delete url timeout` | DELETE |
| `statusCode r`, `isSuccess r`, `raiseForStatus r` | status handling |
| `body r`, `bodyJson r`, `contentLength r` | response payload |
| `getHeader r name default` | total header lookup (never KeyError) |
| `finalUrl r` | URL after redirects |

## A note on the trust boundary

As with every FFI binding, the refinements are **promises the wrapper author
makes**, not facts checked against `requests` itself (see
[the FFI guide](ffi#mental-model)). They are honest here because the underlying
calls really do behave as claimed — `raise_for_status()` raises iff the status
is 4xx/5xx, `timeout=` really does bound the wait. Keep them honest if you extend
the module.
