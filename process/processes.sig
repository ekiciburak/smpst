  process : Type
  part : Type
  label : Type
  sort : Type
  expr: Type
  ltt : Type
  list : Functor
  prod: Functor

  pinact   : process
  psend    : part -> label -> expr -> process -> process
  preceive : part -> "list" ("prod" ("prod" (label, sort), process)) -> process
  pite     : expr -> process -> process -> process
  prec     : ltt -> (process -> process) -> process