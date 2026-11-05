import Provider.Compression.EncodingBounds

/-!
# Certificate transfer through compression

Defines the certificates for the compressed and padded-compressed F2 sources
(`compressedCertificate`, `paddedCompressedCertificate`) and the resulting
verified source `paddedCompressedVerified`. The theorem
`paddedCompressedVerified_literal` records that this verified source is
literal.
-/

namespace Paper.CompressionCertificate

open Paper.F2CatalogTransfer Paper.CompressionF2

def compressedCertificate {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) : F2Certificate (compressedF2 t) where
  weights := cert.weights
  certificate := cert.certificate

def paddedCompressedCertificate {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) (A B : Nat) :
    F2Certificate (paddedCompressedF2 t A B) where
  weights := cert.weights
  certificate := cert.certificate

def paddedCompressedVerified {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) (A B : Nat) : Paper.PPEndToEnd.VerifiedPPCandidate K :=
  (paddedCompressedF2 t A B).toVerified (paddedCompressedCertificate t cert A B)

theorem paddedCompressedVerified_literal {K : Nat} (t : F2Source K)
    (cert : F2Certificate t) (A B : Nat) :
    VerifiedLiteralF2 (paddedCompressedVerified t cert A B) := by
  exact toVerified_literal (paddedCompressedF2 t A B)
    (paddedCompressedCertificate t cert A B)

end Paper.CompressionCertificate
