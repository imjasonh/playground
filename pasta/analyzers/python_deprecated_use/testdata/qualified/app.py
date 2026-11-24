import lib


def use():
    a = lib.old_fn()  # want `old_fn is deprecated`
    b = lib.new_fn()  # OK
    client = lib.Client()
    c = client.post()  # want `post is deprecated`
    d = client.send()  # OK
    return a + b + c + d
