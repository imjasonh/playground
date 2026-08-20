eval("1 + 1")  # want "eval() executes its argument as Python"
eval(user_input)  # want "eval() executes its argument as Python"

# Attribute named eval is not the builtin.
obj.eval()

# compile is a different builtin; leave it alone.
compile("x", "<string>", "eval")
