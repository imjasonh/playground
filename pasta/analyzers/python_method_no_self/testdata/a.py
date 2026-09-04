class Good:
    def ok(self):
        return 1

    def with_args(self, x, y):
        return x + y

    def cls_method(cls, x):  # also acceptable
        return cls

    def annotated(self: "Good") -> int:
        return 0

    def wrapped(
        self,
        child,
    ):
        return child

    def wrapped_cls(
        cls,
        x,
    ):
        return cls

    def wrapped_annotated(
        self: "Good",
        x: int,
    ) -> int:
        return x

    def commented(
        # receiver
        self,
    ):
        return 0

    def positional_only(self, /):
        return 0

    def defaulted(self=None):
        return 0

    def typed_default(self: int = 0):
        return 0


class Bad:
    def no_self():  # want "method `no_self` is missing `self`"
        return 1

    def wrong_name(other):  # want "method `wrong_name` is missing `self`"
        return other

    def wrapped_other(  # want "method `wrapped_other` is missing `self`"
        other,
    ):
        return other

    def starred(*args):  # want "method `starred` is missing `self`"
        return args

    def typed_star(*args: int):  # want "method `typed_star` is missing `self`"
        return args

    def kwargs_only(**kwargs):  # want "method `kwargs_only` is missing `self`"
        return kwargs

    def kw_only(*, x):  # want "method `kw_only` is missing `self`"
        return x


# Top-level functions are fine. Not in a class.
def freestanding():
    return 1


def takes_other(other):
    return other


def wrapped_top(
    other,
):
    return other
