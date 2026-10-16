module Atom = Legacy_atom
module Mixfix = Legacy_mixfix
module Lib = struct
  module Id = struct
    type t = string Common.Source.phrase
    let compare a b = String.compare a.Common.Source.it b.Common.Source.it
    let to_string a = a.Common.Source.it
  end
  module IdSet = struct
    include Set.Make (Id)
    let to_string ?(with_braces = true) s =
      let body = String.concat ", " (List.map Id.to_string (elements s)) in
      if with_braces then "{ " ^ body ^ " }" else body
  end
end
