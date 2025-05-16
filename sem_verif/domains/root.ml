open Domain

module Sign : DOMAIN =
 struct
  module NR_sign = Non_relational (Sign)
  include NR_sign

  let extract_in s in_s = failwith "todo"

  let refine_in s in_s = failwith "todo"

  let extract_out s out_s = failwith "todo"

  let refine_out s out_s = failwith "todo"
 end
