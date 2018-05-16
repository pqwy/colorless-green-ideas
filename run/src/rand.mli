
type g

val inj : Nocrypto.Rng.g -> g
val prj : g -> Nocrypto.Rng.g

val split : g -> g * g

val create : unit -> g
