# The conatural numbers form an exponential commutative semiring

This is the formalization for the paper titled "The conatural numbers form an
exponential commutative semiring". The files are checked with Agda version
2.7.0.1 and the Agda Cubical Library version 0.8.

- agda/ConatDirect.agda: This file contains the
  formalization that conatural numbers form a commutative semiring
  with an exponentiation operation using the method in Section 3 in the paper.
- agda/ConatMultiplication.lagda.tex: This file contains the definition of
  multiplication using the method in Section 4.1.
- agda/ConatDSL: This folder contains the formalization for Section 4.2
  - agda/ConatDSL/Bisimilarity/Base.lagda.tex: This file contains the
    definition of the embedded language used in Section 4.2
  - agda/ConatDSL/Properties.lagda.tex: This file contains the properties of
    addition of conatural numbers, including the commutativity of addition in
    Section 4.2
- agda/ConatQuotiented.agda: This file contains the formalization that conatural
  numbers form an exponential semiring using the method in Section 5.
