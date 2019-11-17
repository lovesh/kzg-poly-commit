# Polynomial Commitments

Based on this [paper](https://pdfs.semanticscholar.org/31eb/add7a0109a584cfbf94b3afaa3c117c78c91.pdf) by Aniket Kate, 
Gregory Zaverucha, Ian Goldberg. The schemes from the paper are modified to work with type-3 pairings.

Since type-3 requires both groups of the bilinear map to be distinct (in addition to other conditions), another group G2 is 
introduced. As a result public key becomes twice the size of whats mentioned in the paper as now for each power of secret key, 
there is an element in both G1 and G2. 
Scheme PolyCommit_DL in section 3.2, for efficiency we can choose the public key elements in G2 (g1^{alpha^i}s) since they 
are used to compute commitment and commitment is done once for each polynomial. The witness is computed in G1 since it is computed once 
for each evaluation. Verification requires 1 exponentiation in G2 in addition to a multi-pairing or e(g1, g2) can be precomputed.
Similarly for PolyCommit_Ped in 3.3, public key elements are in G1 and witness is in G2.

# TODO:
- Batch opening from section 3.4.
- More documentation.
