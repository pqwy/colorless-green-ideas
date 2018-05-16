Set Implicit Arguments.
Set Asymmetric Patterns.

Require Prelude.

Section With_bytes.

  Variable bytes: Set.

  Inductive version :=
    Tls1_0 | Tls1_1 | Tls1_2 | Tls1_3 | Tls1_3_draft (v: nat).

  Definition this_version := Tls1_3_draft 23.

  Inductive hash := Sha1 | Sha256 | Sha384 | Sha512.

  Inductive cipher := 
    Aes_128_gcm | Aes_256_gcm | Chacha20_poly1305 | Aes_128_ccm | Aes_128_ccm_8.

  Inductive ciphersuite :=
    Aes_128_gcm_sha256
  | Aes_256_gcm_sha384
  | Chacha20_poly1305_sha256
  | Aes_128_ccm_sha256
  | Aes_128_ccm_8_sha256
  | Other_ciphersuite (_: nat).

  Inductive signature_scheme :=
    Rsa_pkcs1_sha256
  | Rsa_pkcs1_sha384
  | Rsa_pkcs1_sha512
  | Ecdsa_secp256r1_sha256
  | Ecdsa_secp384r1_sha384
  | Ecdsa_secp521r1_sha512
  | Rsa_pss_rsae_sha256
  | Rsa_pss_rsae_sha384
  | Rsa_pss_rsae_sha512
  | Ed25519
  | Ed448
  | Rsa_pss_pss_sha256
  | Rsa_pss_pss_sha384
  | Rsa_pss_pss_sha512
  | Rsa_pkcs1_sha1
  | Ecdsa_sha1
  | Other_signature_scheme (_: nat).

  Inductive named_group :=
    Secp256r1
  | Secp384r1
  | Secp521r1
  | X25519
  | X448
  | Ffdhe2048
  | Ffdhe3072
  | Ffdhe4096
  | Ffdhe6144
  | Ffdhe8192.

  Inductive psk_kex_mode := Psk_ke | Psk_dhe_ke.

  (* Inductive certificate := *)
  (*   X509         : bytes -> certificate *)
  (* | RawPublicKey : bytes -> certificate. *)

  Inductive extension :=
    Supported_versions   : list version -> extension
  | Supported_version    : version -> extension (* Server's variation of the above.  *)
  | Signature_algorithms : list signature_scheme -> extension
  | Supported_groups     : list named_group -> extension
  | Psk_kex_modes        : list psk_kex_mode -> extension
  | Key_shares           : list (named_group * bytes) -> extension (* ClientHello *)
  | Key_share            : (named_group * bytes) -> extension      (* ServerHello *)
                                                                   (* XXX HelloRetryRequest *)
  | Other_extension      : nat -> bytes -> extension.

  Definition random := bytes.
  Definition ssn_id := bytes. (* _legacy_ session id *)
  Definition certificate_request_ctx := bytes.

  Inductive hs_message :=
    ClientHello         : random -> ssn_id -> list ciphersuite -> list extension -> hs_message
  | ServerHello         : random -> ssn_id -> ciphersuite -> list extension -> hs_message
  | EncryptedExtensions : list extension -> hs_message
  | Certificate         : certificate_request_ctx -> list (bytes * list extension) -> hs_message
  | CertificateRequest  : certificate_request_ctx -> list extension -> hs_message
  | CertificateVerify   : signature_scheme -> bytes -> hs_message
  | Finished            : bytes -> hs_message
  .

  Inductive content_type := Change_cipher_spec | Alert | Handshake | Application_data.

  Inductive record := TLSRecord : content_type -> bytes -> record.

End With_bytes.
