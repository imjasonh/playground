from typing_extensions import deprecated


@deprecated("use new_fn instead")
def old_fn():
    return 1


def new_fn():
    return 2


class Client:
    @deprecated("use send instead")
    def post(self):
        return 3

    def send(self):
        return 4
