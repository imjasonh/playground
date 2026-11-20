def good():
    raise NotImplementedError("to do")


def bad():
    raise NotImplemented  # want "raise NotImplemented raises TypeError at runtime"
