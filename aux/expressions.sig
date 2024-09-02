  expr : Type
  value: Type
  
  eval : value -> expr
  enot : expr -> expr
  egt  : expr -> expr -> expr
  eplus: expr -> expr -> expr
  elam : (expr -> expr) -> expr
  