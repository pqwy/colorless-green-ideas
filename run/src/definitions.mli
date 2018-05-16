open Generated

module Bytes       : Bytes with type bytes = bytes
module Wire        : Wire  with type bytes = bytes
module Crypto_core : Crypto_core with type bytes = bytes and type Rng.g = Rand.g
