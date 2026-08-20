def f(active, foo)
  !!@active  # want "`!!` converts to boolean"
  !!foo      # want "`!!` converts to boolean"
  !@active
  foo
end
