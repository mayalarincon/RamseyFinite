# RamseyFinite
Proof of the finite version of Ramsey's Theorem

Fabián Fernando Serrano Suárez (UNAL - Manizales)

Thaynara Arielly de Lima (Universidade Federal de Goiás)

Mauricio Ayala-Rincón (Universidade Federal de Goiás / Universidade de Brasília)


This entry formalizes the finite version of Ramsey's theorem as a consequence of its infinitary version and of König's lemma, following the proof in Boolos, Burgess and Jeffrey's Computability and Logic. König's lemma is the one formalized in the AFP entry Prop_Compactness as an application of the compactness theorem for propositional logic; it is transferred here from trees whose nodes
belong to a countable type to trees whose set of nodes is countable. Thus, the finite Ramsey theorem is obtained as one more application of propositional compactness, alongside Hall's theorem for countable
families of sets and for countable bipartite graphs, the de Bruijn--Erdös k-coloring theorem and König's lemma, formalized in Prop_Compactness, and the countable version of Dilworth's theorem, formalized in Dilworth\_Countable. In contrast, the infinitary version of Ramsey's theorem, taken from the HOL-Library, is proved directly by induction and does not depend on compactness: in this proof, compactness is needed precisely to pass from the infinite to the finite.
