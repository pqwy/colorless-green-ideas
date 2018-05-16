
open Nocrypto

let n = 32
type g = Cstruct.t

let inj g = Rng.generate ~g n
let prj g = Rng.create ~seed:g (module Rng.Generators.Fortuna)

let split g = Cstruct.split (Rng.generate ~g:(prj g) (2 * n)) n

let create () = inj !Rng.generator
