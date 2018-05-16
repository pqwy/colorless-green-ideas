open Definitions
module Proto = Generated.Make_proto (Bytes) (Crypto_core) (Wire)
module Crypto = Generated.Make_crypto (Bytes) (Crypto_core)
