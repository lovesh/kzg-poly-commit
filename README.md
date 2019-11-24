# Polynomial Commitments

Based on the paper [Polynomial Commitments](https://pdfs.semanticscholar.org/31eb/add7a0109a584cfbf94b3afaa3c117c78c91.pdf) by Aniket Kate, 
Gregory Zaverucha, Ian Goldberg. The schemes from the paper are modified to work with type-3 pairings.

Since type-3 requires both groups of the bilinear map to be distinct (in addition to other conditions), another group G2 is 
introduced. As a result public key becomes twice the size of whats mentioned in the paper as now for each power of secret key, 
there is an element in both G1 and G2.  
Scheme PolyCommit_DL in section 3.2, for efficiency we can choose the public key elements in G2 (g2^{alpha^i}s) to compute commitment 
since commitment is done once for each polynomial. The witness is computed in G1 since it is computed once 
for each evaluation. Verification requires 1 exponentiation in G2 in addition to a multi-pairing. There are precomputations possible, 
look at the verification methods for comments.  
Similarly for PolyCommit_Ped in 3.3, commitment is in G1 and witness is in G2.
For more details look at the code comments.

For batch openings, look at functions `create_witness_for_batch` and `verify_eval_for_batch` in both `PolyCommit_DL` and `PolyCommit_Ped`. 
Run tests `timing_batch_witness_random_poly` in both `PolyCommit_DL` and `PolyCommit_Ped` in release mode to see the time it takes for 
creating and verifying the witness for various degree polynomials and for various batch sizes.  

## TODO:
- Compare timing for batch opening vs independent openings 
- Error handling. Start by converting asserts into errors.
- Address TODOs in code
- More documentation.
