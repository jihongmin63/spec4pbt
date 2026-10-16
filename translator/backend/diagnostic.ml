open Common.Source

type t = { region : region; message : string; source : string }
let error ~source region message = { region; message; source }
let render diagnostic =
  Common.Source.string_of_region diagnostic.region ^ " " ^ diagnostic.source ^ ": " ^ diagnostic.message
