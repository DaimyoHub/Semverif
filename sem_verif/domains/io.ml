open States

module In = 
 struct
  (* An input abstract state is just a product of each kind of abstract state of the
     analysis *)
  type t = {
    intvl : intvl;
    sign : sign;
  }
 end

module Out =
 struct
  type t = 
    | Intvl of intvl
    | Sign of sign
 end
