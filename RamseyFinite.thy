(* Ramsey's Theorem (finitary version) as a consequence of the
   Infinitary Ramsey's Theorem and of König's Lemma, following

     G. S. Boolos, J. P. Burgess, R. C. Jeffrey,
     "Computability and Logic", 5th ed., Chapter 26:
       26.1 Theorem (Ramsey's theorem)
       26.2 Theorem (Infinitary Ramsey's theorem)
       26.3 Lemma   (König's lemma)

   An application of the compactness theorem of propositional logic: the
   proof goes through König's lemma, which is obtained from the compactness
   theorem in the AFP entry Prop_Compactness.

   Thaynara Arielly de Lima        Universidade Federal de Goiás
   Mauricio Ayala-Rincón           Universidade de Brasília and
                                   Universidade Federal de Goiás
   Fabián Fernando Serrano Suárez  Universidad Nacional de Colombia

   Last modified:  6 November 2026
*)

theory RamseyFinite
imports 
  "HOL-Library.Ramsey"
  "Prop_Compactness.KoenigLemma"

begin

section \<open>Ramsey's Theorem (finitary version)\<close>

text \<open>This theory formalizes Ramsey's theorem \<^cite>\<open>Ramsey1930\<close> in its finitary
  version, following the presentation of Boolos, Burgess and Jeffrey
  \<^cite>\<open>BoolosBJ2007\<close>.  The finitary Ramsey theorem (Theorem 26.1) is obtained, as
  in the book, by a detour through the infinite: it follows from the infinitary
  version (Theorem 26.2, theorem @{thm [source] Ramsey.Ramsey} of
  \<^theory>\<open>HOL-Library.Ramsey\<close>) together with König's lemma \<^cite>\<open>Koenig1927\<close>
  (Lemma 26.3, theorem @{thm [source] Koenig_Lemma} of the theory
  \<^theory>\<open>Prop_Compactness.KoenigLemma\<close>, proved there from the compactness
  theorem of propositional logic).

  The development proceeds in five steps:
  \<^enum> Theorem 26.2, the infinitary Ramsey theorem, restated in the notation of
    the book;
  \<^enum> König's lemma, transferred from trees whose nodes belong to a countable
    type to trees whose set of nodes is countable;
  \<^enum> the tree of partitions of \<open>[{0,\<dots>,m-1}]\<^bsup>r\<^esup>\<close> having no size-\<open>n\<close>
    homogeneous set, ordered by extension;
  \<^enum> the proof that this tree is infinite when Theorem 26.1 fails;
  \<^enum> Theorem 26.1 itself: König's lemma yields an infinite branch, whose
    partitions glue together into a partition of \<open>[\<omega>]\<^bsup>r\<^esup>\<close>; an infinite
    homogeneous set of the latter, given by Theorem 26.2, contains a size-\<open>n\<close>
    homogeneous set of a node of the tree, a contradiction.

  References to the book are to its 5th edition \<^cite>\<open>BoolosBJ2007\<close>.  The
  infinitary theorem was first formalized in Isabelle/HOL by Ridge
  \<^cite>\<open>"Ramsey-Infinite-AFP"\<close>, following the 3rd edition of the book; that
  development has since been incorporated into \<^theory>\<open>HOL-Library.Ramsey\<close>,
  whose theorem @{thm [source] Ramsey.Ramsey} is used here.\<close>


subsection \<open>An application of the compactness theorem\<close>

text \<open>This theory is one more application of the compactness theorem of
  propositional logic, formalized in the AFP entry \<open>Prop_Compactness\<close>
  \<^cite>\<open>SerranoAFP2024\<close>, which follows the model existence approach of Smullyan
  and Fitting \<^cite>\<open>Smullyan and Fitting\<close> and builds on an earlier Isar
  formalization of first-order meta-logic \<^cite>\<open>Serrano2011\<close>.  That entry
  obtains from compactness Hall's theorem for countable families of sets
  \<^cite>\<open>Serrano2022\<close> and for countable bipartite graphs \<^cite>\<open>Serrano2024\<close>, the
  de Bruijn--Erdős \<open>k\<close>-colouring theorem for infinite graphs
  \<^cite>\<open>DeBruijnErdos1951\<close> and König's lemma; the countable version of Dilworth's
  theorem, in the AFP entry \<open>Dilworth_Countable\<close> \<^cite>\<open>"Dilworth_Countable-AFP"\<close>
  (see also \<^cite>\<open>SerranoLANMR2026\<close>), also builds on it.

  The finite Ramsey theorem depends on compactness through König's lemma, along
  the following chain:
  \<^item> @{thm [source] Compactness_Theorem} (theory
    \<^theory>\<open>Prop_Compactness.PropCompactness\<close>): a set of propositional formulas
    is satisfiable if every finite subset of it is satisfiable;
  \<^item> @{thm [source] Koenig_Lemma} (theory \<^theory>\<open>Prop_Compactness.KoenigLemma\<close>),
    proved directly from compactness: an infinite, finitely branching tree is
    described by a set of formulas whose propositional letters are its nodes,
    stating that each level contains a chosen node, that the predecessors of
    a chosen node are chosen, and that no two nodes of a level are chosen.
    Every finite subset of this set is satisfiable, since the tree has nodes
    at all levels; by compactness the whole set is satisfiable, and the nodes
    true under a satisfying valuation form an infinite path;
  \<^item> \<open>Koenig_Lemma_countable\<close> (below) transfers König's lemma to trees
    whose \<^emph>\<open>set\<close> of nodes is countable;
  \<^item> \<open>Ramsey_Theorem\<close> (below) applies it to the tree of partitions without
    size-\<open>n\<close> homogeneous sets.

  In contrast, and perhaps surprisingly, the infinitary Ramsey theorem does not
  depend on compactness at all.  The theorem @{thm [source] Ramsey.Ramsey} of
  \<^theory>\<open>HOL-Library.Ramsey\<close> is proved there by induction on the size \<open>r\<close> of
  the subsets, with no use of logic.  Thus the infinite statement has a direct
  combinatorial proof, while its finite consequence, obtained from it as in the
  book, needs compactness: compactness is used precisely to pass from the
  infinite to the finite.

  This dependency is a feature of the proof, not of the theorem:
  \<^theory>\<open>HOL-Library.Ramsey\<close> also contains purely finitary proofs of the finite
  Ramsey theorem, which give explicit upper bounds for \<open>m\<close>, starting with the
  bound of Erdős and Szekeres \<^cite>\<open>ErdosSzekeres1935\<close>.  The proof
  formalized here is non-constructive: it shows that \<open>m\<close> exists without
  bounding it.\<close>


subsection \<open>Notation\<close>

text \<open>As in the book, \<open>\<omega>\<close> is the set of natural numbers and \<open>[X]\<^bsup>r\<^esup>\<close> is the
  collection of all size-\<open>r\<close> subsets of \<open>X\<close> (notation \<open>nsets\<close> of
  \<open>HOL-Library.Ramsey\<close>).  A partition of \<open>[X]\<^bsup>r\<^esup>\<close> into \<open>s\<close> classes is a function
  \<open>f : [X]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close>, written \<open>f \<in> [X]\<^bsup>r\<^esup> \<rightarrow> {1..s}\<close>; a set \<open>Y\<close> is
  homogeneous for \<open>f\<close> when \<open>f : [Y]\<^bsup>r\<^esup> \<rightarrow> {j}\<close> for some \<open>j\<close>.\<close>

abbreviation omega :: "nat set" (\<open>\<omega>\<close>)
  where "\<omega> \<equiv> UNIV"

text \<open>\<open>homogeneous r f Y\<close> states that \<open>Y\<close> is homogeneous for the partition \<open>f\<close>
  of the size-\<open>r\<close> sets: \<open>f\<close> takes a single value on \<open>[Y]\<^bsup>r\<^esup>\<close>.  It is an
  abbreviation, hence it is unfolded when the theory is parsed and the proofs
  below work directly on its expansion.\<close>

abbreviation homogeneous :: "nat \<Rightarrow> ('a set \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "homogeneous r f Y \<equiv> \<exists>j. f \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j}"


subsection \<open>Theorem 26.2 (Infinitary Ramsey's theorem)\<close>

text \<open>Statement of Theorem 26.2 in the notation of the book: if
  \<open>f : [\<omega>]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close>, then there is an infinite \<open>Y \<subseteq> \<omega>\<close> and a \<open>j\<close> with
  \<open>1 \<le> j \<le> s\<close> such that \<open>f : [Y]\<^bsup>r\<^esup> \<rightarrow> {j}\<close>.  It is a direct reformulation of
  the theorem @{thm [source] Ramsey.Ramsey} (with \<open>s+1\<close> colours \<open>0,\<dots>,s\<close>).  This step does not
  use the compactness theorem.\<close>

theorem Infinitary_Ramsey_Theorem:
  fixes r s :: nat
  assumes "0 < r" and "0 < s"
    and f: "f \<in> [\<omega>]\<^bsup>r\<^esup> \<rightarrow> {1..s}"
  shows "\<exists>Y \<subseteq> \<omega>. infinite Y \<and> (\<exists>j \<in> {1..s}. f \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j})"
proof -
  have "\<forall>X. X \<subseteq> \<omega> \<and> finite X \<and> card X = r \<longrightarrow> f X < Suc s"
  proof (intro allI impI)
    fix X
    assume "X \<subseteq> \<omega> \<and> finite X \<and> card X = r"
    hence "X \<in> [\<omega>]\<^bsup>r\<^esup>" by (simp add: nsets_def)
    hence "f X \<in> {1..s}" using f by (rule funcset_mem[rotated])
    thus "f X < Suc s" by simp
  qed
  moreover have "infinite \<omega>" by simp
  ultimately obtain Y j where Y: "Y \<subseteq> \<omega>" "infinite Y"
    and hom: "\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = r \<longrightarrow> f X = j"
    using Ramsey.Ramsey[where Z = \<omega> and s = "Suc s" and r = r and f = f]
    by blast
  have fY: "f \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j}"
    using hom by (auto simp: nsets_def)
  obtain X where X: "X \<subseteq> Y" "finite X" "card X = r"
    using infinite_arbitrarily_large[OF Y(2)] by blast
  hence "X \<in> [\<omega>]\<^bsup>r\<^esup>" by (simp add: nsets_def)
  hence "f X \<in> {1..s}" using f by (rule funcset_mem[rotated])
  moreover have "f X = j" using hom X by blast
  ultimately have "j \<in> {1..s}" by simp
  thus ?thesis using Y fY by blast
qed


subsection \<open>König's lemma for trees with a countable set of nodes\<close>

text \<open>This is where the compactness theorem enters the proof: the theorem
  \<open>Koenig_Lemma\<close> used below is proved from it in the theory \<open>KoenigLemma\<close>.

  In the theory \<open>KoenigLemma\<close> the nodes of the tree must belong to a
  countable \<^emph>\<open>type\<close>.  The nodes of the tree used in the proof of Theorem 26.1
  are partitions, i.e. functions on sets of natural numbers, whose type is not
  countable, although the \<^emph>\<open>set\<close> of nodes is countable.  Hence we first transfer
  König's lemma to trees whose set of nodes is countable, by means of an
  injective map into the natural numbers.

  The idea is a relabelling of the nodes: if \<open>h\<close> is injective on the set \<open>A\<close>
  of nodes, the image of the tree \<open>(A, r)\<close> under \<open>h\<close> is the tree
  \<open>(h ` A, rel_image h r)\<close>, and each notion involved in König's lemma
  (predecessors, height, strict partial order, minimum, tree, immediate
  successors, finite branching, path) is preserved by this relabelling.  Taking
  for \<open>h\<close> an injection of \<open>A\<close> into \<open>nat\<close>, König's lemma applies to the image
  tree, and the infinite path it provides is carried back to \<open>(A, r)\<close> through
  the inverse of \<open>h\<close>.

  The relation \<open>rel_image h r\<close> is the image of \<open>r\<close> under \<open>h\<close> applied to both
  components, i.e. \<open>map_prod h h ` r\<close> in the notation of the library.\<close>

definition rel_image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('b \<times> 'b) set" where
  "rel_image h r = (\<lambda>(x, y). (h x, h y)) ` r"

lemma rel_image_iff:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and x: "x \<in> A" and y: "y \<in> A"
  shows "(h x, h y) \<in> rel_image h r \<longleftrightarrow> (x, y) \<in> r"
proof
  assume "(h x, h y) \<in> rel_image h r"
  then obtain u v where uv: "(u, v) \<in> r" and hu: "h u = h x" and hv: "h v = h y"
    unfolding rel_image_def by auto
  have "u \<in> A" and "v \<in> A" using uv r by auto
  hence "u = x" and "v = y" using hu hv h x y by (auto dest: inj_onD)
  thus "(x, y) \<in> r" using uv by simp
next
  assume "(x, y) \<in> r"
  thus "(h x, h y) \<in> rel_image h r" unfolding rel_image_def by force
qed

lemma rel_image_subset:
  assumes "r \<subseteq> A \<times> A"
  shows "rel_image h r \<subseteq> h ` A \<times> h ` A"
  using assms unfolding rel_image_def by auto

lemma predecessors_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and a: "a \<in> A"
  shows "predecessors (h ` A) (h a) (rel_image h r) = h ` predecessors A a r"
proof
  show "predecessors (h ` A) (h a) (rel_image h r) \<subseteq> h ` predecessors A a r"
  proof
    fix u
    assume "u \<in> predecessors (h ` A) (h a) (rel_image h r)"
    hence u: "u \<in> h ` A" "(u, h a) \<in> rel_image h r"
      by (simp_all add: predecessors_def)
    then obtain x where x: "x \<in> A" "u = h x" by auto
    have "(x, a) \<in> r" using u(2) x rel_image_iff[OF h r x(1) a] by simp
    thus "u \<in> h ` predecessors A a r" using x by (auto simp: predecessors_def)
  qed
next
  show "h ` predecessors A a r \<subseteq> predecessors (h ` A) (h a) (rel_image h r)"
  proof
    fix u
    assume "u \<in> h ` predecessors A a r"
    then obtain x where x: "x \<in> A" "(x, a) \<in> r" "u = h x"
      by (auto simp: predecessors_def)
    have "(h x, h a) \<in> rel_image h r" using x(2) rel_image_iff[OF h r x(1) a] by simp
    thus "u \<in> predecessors (h ` A) (h a) (rel_image h r)"
      using x by (auto simp: predecessors_def)
  qed
qed

lemma height_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and a: "a \<in> A"
  shows "height (h ` A) (h a) (rel_image h r) = height A a r"
proof -
  have "predecessors A a r \<subseteq> A" by (auto simp: predecessors_def)
  hence "inj_on h (predecessors A a r)" using h inj_on_subset by blast
  thus ?thesis using predecessors_image[OF h r a] by (simp add: height_def card_image)
qed

lemma total_on_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and P: "P \<subseteq> A"
    and t: "total_on P r"
  shows "total_on (h ` P) (rel_image h r)"
proof (unfold total_on_def, intro ballI impI)
  fix u v
  assume "u \<in> h ` P" and "v \<in> h ` P" and uv: "u \<noteq> v"
  then obtain x y where x: "x \<in> P" "u = h x" and y: "y \<in> P" "v = h y" by auto
  have "x \<noteq> y" using uv x y by auto
  hence "(x, y) \<in> r \<or> (y, x) \<in> r" using t x(1) y(1) unfolding total_on_def by blast
  thus "(u, v) \<in> rel_image h r \<or> (v, u) \<in> rel_image h r"
    using x y unfolding rel_image_def by force
qed

lemma spo_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and spo: "strict_part_order A r"
  shows "strict_part_order (h ` A) (rel_image h r)"
proof -
  have irr: "irrefl_on A r" and tr: "trans_on A r"
    using spo by (auto simp: strict_part_order_def)
  have "irrefl_on (h ` A) (rel_image h r)"
  proof (unfold irrefl_on_def, intro ballI)
    fix u
    assume "u \<in> h ` A"
    then obtain x where x: "x \<in> A" "u = h x" by auto
    have "(x, x) \<notin> r" using irr x(1) unfolding irrefl_on_def by blast
    thus "(u, u) \<notin> rel_image h r" using rel_image_iff[OF h r x(1) x(1)] x(2) by simp
  qed
  moreover have "trans_on (h ` A) (rel_image h r)"
  proof (unfold trans_on_def, intro ballI impI)
    fix u v w
    assume "u \<in> h ` A" "v \<in> h ` A" "w \<in> h ` A"
      and uv: "(u, v) \<in> rel_image h r" and vw: "(v, w) \<in> rel_image h r"
    then obtain x y z where x: "x \<in> A" "u = h x" and y: "y \<in> A" "v = h y"
      and z: "z \<in> A" "w = h z" by auto
    have "(x, y) \<in> r" using uv rel_image_iff[OF h r x(1) y(1)] x(2) y(2) by simp
    moreover have "(y, z) \<in> r" using vw rel_image_iff[OF h r y(1) z(1)] y(2) z(2) by simp
    ultimately have "(x, z) \<in> r" using tr x(1) y(1) z(1) unfolding trans_on_def by blast
    thus "(u, w) \<in> rel_image h r" using rel_image_iff[OF h r x(1) z(1)] x(2) z(2) by simp
  qed
  ultimately show ?thesis by (simp add: strict_part_order_def)
qed

lemma minimum_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and m: "minimum A a r"
  shows "minimum (h ` A) (h a) (rel_image h r)"
proof -
  have a: "a \<in> A" and min: "\<forall>x\<in>A. x \<noteq> a \<longrightarrow> (a, x) \<in> r"
    using m by (auto simp: minimum_def)
  have "\<forall>u \<in> h ` A. u \<noteq> h a \<longrightarrow> (h a, u) \<in> rel_image h r"
  proof (intro ballI impI)
    fix u
    assume "u \<in> h ` A" and ua: "u \<noteq> h a"
    then obtain x where x: "x \<in> A" "u = h x" by auto
    hence "x \<noteq> a" using ua by auto
    hence "(a, x) \<in> r" using min x(1) by simp
    thus "(h a, u) \<in> rel_image h r" using rel_image_iff[OF h r a x(1)] x(2) by simp
  qed
  thus ?thesis using a by (simp add: minimum_def)
qed

lemma tree_image:
  assumes h: "inj_on h A" and t: "tree A r"
  shows "tree (h ` A) (rel_image h r)"
proof -
  have r: "r \<subseteq> A \<times> A" and rne: "r \<noteq> {}" and spo: "strict_part_order A r"
    and min: "\<exists>a. minimum A a r"
    and preds: "\<forall>a\<in>A. finite (predecessors A a r) \<and> total_on (predecessors A a r) r"
    using t unfolding tree_def by auto
  have "rel_image h r \<subseteq> h ` A \<times> h ` A" using r by (rule rel_image_subset)
  moreover have "rel_image h r \<noteq> {}" using rne by (simp add: rel_image_def)
  moreover have "strict_part_order (h ` A) (rel_image h r)" using spo_image[OF h r spo] .
  moreover have "\<exists>b. minimum (h ` A) b (rel_image h r)"
    using min minimum_image[OF h r] by blast
  moreover have "\<forall>b \<in> h ` A. finite (predecessors (h ` A) b (rel_image h r)) \<and>
                   total_on (predecessors (h ` A) b (rel_image h r)) (rel_image h r)"
  proof
    fix b
    assume "b \<in> h ` A"
    then obtain a where a: "a \<in> A" "b = h a" by auto
    have eq: "predecessors (h ` A) b (rel_image h r) = h ` predecessors A a r"
      using predecessors_image[OF h r a(1)] a(2) by simp
    have "finite (predecessors A a r)" and tot: "total_on (predecessors A a r) r"
      using preds a(1) by auto
    moreover have "predecessors A a r \<subseteq> A" by (auto simp: predecessors_def)
    ultimately show "finite (predecessors (h ` A) b (rel_image h r)) \<and>
                     total_on (predecessors (h ` A) b (rel_image h r)) (rel_image h r)"
      using eq total_on_image[OF h r] by simp
  qed
  ultimately show ?thesis by (simp add: tree_def)
qed

lemma imm_successors_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and a: "a \<in> A"
  shows "imm_successors (h ` A) (h a) (rel_image h r) = h ` imm_successors A a r"
proof
  show "imm_successors (h ` A) (h a) (rel_image h r) \<subseteq> h ` imm_successors A a r"
  proof
    fix u
    assume "u \<in> imm_successors (h ` A) (h a) (rel_image h r)"
    hence u: "u \<in> h ` A" "(h a, u) \<in> rel_image h r"
      "height (h ` A) u (rel_image h r) = height (h ` A) (h a) (rel_image h r) + 1"
      by (simp_all add: imm_successors_def)
    then obtain x where x: "x \<in> A" "u = h x" by auto
    have "(a, x) \<in> r" using u(2) x rel_image_iff[OF h r a x(1)] by simp
    moreover have "height A x r = height A a r + 1"
      using u(3) x height_image[OF h r x(1)] height_image[OF h r a] by simp
    ultimately show "u \<in> h ` imm_successors A a r"
      using x by (auto simp: imm_successors_def)
  qed
next
  show "h ` imm_successors A a r \<subseteq> imm_successors (h ` A) (h a) (rel_image h r)"
  proof
    fix u
    assume "u \<in> h ` imm_successors A a r"
    then obtain x where x: "x \<in> A" "(a, x) \<in> r" "height A x r = height A a r + 1"
      "u = h x" by (auto simp: imm_successors_def)
    have "(h a, u) \<in> rel_image h r" using rel_image_iff[OF h r a x(1)] x by simp
    moreover have "height (h ` A) u (rel_image h r) = height (h ` A) (h a) (rel_image h r) + 1"
      using x height_image[OF h r x(1)] height_image[OF h r a] by simp
    ultimately show "u \<in> imm_successors (h ` A) (h a) (rel_image h r)"
      using x by (auto simp: imm_successors_def)
  qed
qed

lemma finitely_branching_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and fb: "finitely_branching A r"
  shows "finitely_branching (h ` A) (rel_image h r)"
proof (unfold finitely_branching_def, intro ballI)
  fix b
  assume "b \<in> h ` A"
  then obtain a where a: "a \<in> A" "b = h a" by auto
  have "finite (imm_successors A a r)" using fb a(1) by (simp add: finitely_branching_def)
  thus "finite (imm_successors (h ` A) b (rel_image h r))"
    using imm_successors_image[OF h r a(1)] a(2) by simp
qed

lemma path_image:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A" and p: "path B A r"
  shows "path (h ` B) (h ` A) (rel_image h r)"
proof -
  have BA: "B \<subseteq> A" and spo: "strict_part_order A r" and tot: "total_on B r"
    and max: "\<forall>C. B \<subseteq> C \<and> sub_linear_order C A r \<longrightarrow> B = C"
    using p by (auto simp: path_def sub_linear_order_def)
  have slo: "sub_linear_order (h ` B) (h ` A) (rel_image h r)"
    using BA spo_image[OF h r spo] total_on_image[OF h r BA tot]
    by (auto simp: sub_linear_order_def)
  have "h ` B = C'"
    if C': "h ` B \<subseteq> C'" "sub_linear_order C' (h ` A) (rel_image h r)" for C'
  proof -
    let ?g = "inv_into A h"
    let ?C = "?g ` C'"
    have C'A: "C' \<subseteq> h ` A" and totC': "total_on C' (rel_image h r)"
      using C'(2) by (auto simp: sub_linear_order_def)
    have hC: "h ` ?C = C'" using image_inv_into_cancel[OF refl C'A] .
    have CA: "?C \<subseteq> A" using C'A by (auto intro: inv_into_into)
    have "total_on ?C r"
    proof (unfold total_on_def, intro ballI impI)
      fix x y
      assume x: "x \<in> ?C" and y: "y \<in> ?C" and xy: "x \<noteq> y"
      have xA: "x \<in> A" and yA: "y \<in> A" using x y CA by auto
      have "h x \<in> C'" and "h y \<in> C'" using x y hC by auto
      moreover have "h x \<noteq> h y" using xy xA yA h by (auto dest: inj_onD)
      ultimately have "(h x, h y) \<in> rel_image h r \<or> (h y, h x) \<in> rel_image h r"
        using totC' unfolding total_on_def by blast
      thus "(x, y) \<in> r \<or> (y, x) \<in> r"
        using rel_image_iff[OF h r xA yA] rel_image_iff[OF h r yA xA] by simp
    qed
    hence "sub_linear_order ?C A r" using CA spo by (simp add: sub_linear_order_def)
    moreover have "B \<subseteq> ?C"
    proof
      fix b
      assume b: "b \<in> B"
      hence "h b \<in> C'" using C'(1) by auto
      moreover have "?g (h b) = b" using b BA h by auto
      ultimately show "b \<in> ?C" by force
    qed
    ultimately have "B = ?C" using max by blast
    thus "h ` B = C'" using hC by simp
  qed
  thus ?thesis using slo unfolding path_def by blast
qed

text \<open>Relabelling by \<open>h\<close> and then by its inverse gives back the original relation.\<close>

lemma rel_image_inv_into:
  assumes h: "inj_on h A" and r: "r \<subseteq> A \<times> A"
  shows "rel_image (inv_into A h) (rel_image h r) = r"
proof
  show "rel_image (inv_into A h) (rel_image h r) \<subseteq> r"
  proof
    fix p
    assume "p \<in> rel_image (inv_into A h) (rel_image h r)"
    then obtain x y where xy: "(x, y) \<in> r" and p: "p = (inv_into A h (h x), inv_into A h (h y))"
      unfolding rel_image_def by auto
    have "x \<in> A" and "y \<in> A" using xy r by auto
    thus "p \<in> r" using p xy h by simp
  qed
next
  show "r \<subseteq> rel_image (inv_into A h) (rel_image h r)"
  proof
    fix p
    assume p: "p \<in> r"
    then obtain x y where xy: "p = (x, y)" by (cases p) auto
    have "x \<in> A" and "y \<in> A" using p xy r by auto
    hence "p = (inv_into A h (h x), inv_into A h (h y))" using xy h by simp
    thus "p \<in> rel_image (inv_into A h) (rel_image h r)"
      using p xy unfolding rel_image_def by force
  qed
qed

theorem Koenig_Lemma_countable:
  assumes t: "tree A r" and c: "countable A" and inf: "infinite A"
    and fb: "finitely_branching A r"
  shows "\<exists>B. infinite_path B A r"
proof -
  let ?h = "to_nat_on A"
  have h: "inj_on ?h A" using c by (rule inj_on_to_nat_on)
  have r: "r \<subseteq> A \<times> A" using t by (simp add: tree_def)
  have "infinite_tree (?h ` A) (rel_image ?h r)"
    using tree_image[OF h t] inf finite_image_iff[OF h] by simp
  moreover have "finitely_branching (?h ` A) (rel_image ?h r)"
    using finitely_branching_image[OF h r fb] .
  ultimately obtain B' where B': "infinite_path B' (?h ` A) (rel_image ?h r)"
    using Koenig_Lemma by blast
  hence pB': "path B' (?h ` A) (rel_image ?h r)" and iB': "infinite B'"
    by (simp_all add: infinite_path_def)
  have B'A: "B' \<subseteq> ?h ` A" using pB' by (simp add: path_def sub_linear_order_def)
  let ?g = "inv_into A ?h"
  have g: "inj_on ?g (?h ` A)" by (rule inj_on_inv_into) simp
  have r': "rel_image ?h r \<subseteq> ?h ` A \<times> ?h ` A" using r by (rule rel_image_subset)
  have gA: "?g ` ?h ` A = A" using h by simp
  have gr: "rel_image ?g (rel_image ?h r) = r" using rel_image_inv_into[OF h r] .
  have "path (?g ` B') A r" using path_image[OF g r' pB'] gA gr by simp
  moreover have "infinite (?g ` B')"
    using iB' finite_image_iff[OF inj_on_subset[OF g B'A]] by simp
  ultimately show ?thesis by (auto simp: infinite_path_def)
qed


subsection \<open>The tree of partitions without size-\<open>n\<close> homogeneous sets\<close>

text \<open>The nodes of the tree are the pairs \<open>(m, f)\<close> where
  \<open>f : [{0,\<dots>,m-1}]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close> is a partition having no size-\<open>n\<close>
  homogeneous set.  The partition \<open>f\<close> is taken extensional (it takes the
  value \<open>undefined\<close> outside its domain), so that it is determined by its values
  on \<open>[{0,\<dots>,m-1}]\<^bsup>r\<^esup>\<close>.  The node \<open>(m, f)\<close> lies at level \<open>m\<close>.

  In the book the levels are \<open>T\<^sub>k\<close>, formed by the partitions with \<open>m = n + k\<close>.
  The formalization of König's lemma requires a tree with a single root, so here
  all values \<open>m \<ge> 0\<close> are used: the root is the empty partition (\<open>m = 0\<close>), and
  for \<open>m < n\<close> no partition has a size-\<open>n\<close> homogeneous set.

  The book relates \<open>f\<close> and \<open>g\<close> when \<open>g\<close> is at the next level and extends \<open>f\<close>;
  the formalized König's lemma uses the corresponding strict order, so \<open>f\<close> is
  related with \<open>g\<close> when \<open>g\<close> is at a higher level and extends \<open>f\<close>, i.e. \<open>g\<close>
  assigns the same value as does \<open>f\<close> to any argument in the domain of \<open>f\<close>.

  Accordingly, \<open>Tnodes r s n\<close> is the set of nodes of the tree (the partitions
  without size-\<open>n\<close> homogeneous sets, paired with their levels), and
  \<open>Rext r s n\<close> is the extension order between them.\<close>

definition Tnodes :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat set \<Rightarrow> nat)) set" where
  "Tnodes r s n = {(m, f). f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s} \<and>
                           \<not> (\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r f Y)}"

definition Rext ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> (nat set \<Rightarrow> nat)) \<times> (nat \<times> (nat set \<Rightarrow> nat))) set" where
  "Rext r s n = {((m, f), (m', g)). (m, f) \<in> Tnodes r s n \<and> (m', g) \<in> Tnodes r s n \<and>
                    m < m' \<and> (\<forall>x \<in> [{0..<m}]\<^bsup>r\<^esup>. g x = f x)}"

lemma Tnodes_iff:
  "(m, f) \<in> Tnodes r s n \<longleftrightarrow>
     f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s} \<and> \<not> (\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r f Y)"
  by (simp add: Tnodes_def)

lemma Rext_iff:
  "((m, f), (m', g)) \<in> Rext r s n \<longleftrightarrow>
     (m, f) \<in> Tnodes r s n \<and> (m', g) \<in> Tnodes r s n \<and> m < m' \<and>
     (\<forall>x \<in> [{0..<m}]\<^bsup>r\<^esup>. g x = f x)"
  by (simp add: Rext_def)

lemma nsets_interval_mono:
  fixes m m' :: nat
  assumes "m \<le> m'"
  shows "[{0..<m}]\<^bsup>r\<^esup> \<subseteq> [{0..<m'}]\<^bsup>r\<^esup>"
  using assms by (intro nsets_mono) auto

lemma nsets_interval_zero:
  assumes "0 < r"
  shows "[{0..<0::nat}]\<^bsup>r\<^esup> = {}"
  using assms by (auto simp: nsets_def)

text \<open>Restricting a partition without size-\<open>n\<close> homogeneous sets to a smaller
  initial segment gives a node of the tree.\<close>

lemma node_restrict:
  assumes f: "f \<in> [{0..<M}]\<^bsup>r\<^esup> \<rightarrow> {1..s}"
    and noh: "\<not> (\<exists>Y \<in> [{0..<M}]\<^bsup>n\<^esup>. homogeneous r f Y)"
    and mM: "m \<le> M"
  shows "(m, restrict f ([{0..<m}]\<^bsup>r\<^esup>)) \<in> Tnodes r s n"
proof -
  let ?D = "[{0..<m}]\<^bsup>r\<^esup>"
  have sub: "?D \<subseteq> [{0..<M}]\<^bsup>r\<^esup>" using mM by (rule nsets_interval_mono)
  have "\<forall>x \<in> ?D. f x \<in> {1..s}" using f sub by (auto intro: funcset_mem)
  hence 1: "restrict f ?D \<in> ?D \<rightarrow>\<^sub>E {1..s}" by (simp add: restrict_PiE_iff)
  have 2: "\<not> (\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r (restrict f ?D) Y)"
  proof
    assume "\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r (restrict f ?D) Y"
    then obtain Y j where Y: "Y \<in> [{0..<m}]\<^bsup>n\<^esup>"
      and hj: "restrict f ?D \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j}" by blast
    have Ym: "Y \<subseteq> {0..<m}" using Y by (simp add: nsets_def)
    have "Y \<in> [{0..<M}]\<^bsup>n\<^esup>" using Y nsets_interval_mono[OF mM] by blast
    moreover have "f \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j}"
    proof (rule Pi_I)
      fix x
      assume x: "x \<in> [Y]\<^bsup>r\<^esup>"
      hence xD: "x \<in> ?D" using Ym nsets_mono by blast
      have "restrict f ?D x \<in> {j}" using hj x by (rule funcset_mem)
      thus "f x \<in> {j}" using xD by simp
    qed
    ultimately show False using noh by blast
  qed
  from 1 2 show ?thesis by (simp add: Tnodes_def)
qed

lemma node_restrict_node:
  assumes g: "(M, g) \<in> Tnodes r s n" and mM: "m \<le> M"
  shows "(m, restrict g ([{0..<m}]\<^bsup>r\<^esup>)) \<in> Tnodes r s n"
proof (rule node_restrict[OF _ _ mM])
  show "g \<in> [{0..<M}]\<^bsup>r\<^esup> \<rightarrow> {1..s}" using g by (simp add: Tnodes_def PiE_def)
  show "\<not> (\<exists>Y \<in> [{0..<M}]\<^bsup>n\<^esup>. homogeneous r g Y)" using g by (simp add: Tnodes_def)
qed

lemma node_restrict_eq:
  assumes "(m, g) \<in> Tnodes r s n"
  shows "restrict g ([{0..<m}]\<^bsup>r\<^esup>) = g"
  using assms by (auto simp: Tnodes_def)

text \<open>Two restrictions of the same node are related in the tree.\<close>

lemma Rext_restrict:
  assumes g: "(M, g) \<in> Tnodes r s n" and m12: "m1 < m2" and m2M: "m2 \<le> M"
  shows "((m1, restrict g ([{0..<m1}]\<^bsup>r\<^esup>)), (m2, restrict g ([{0..<m2}]\<^bsup>r\<^esup>))) \<in> Rext r s n"
proof -
  have 1: "(m1, restrict g ([{0..<m1}]\<^bsup>r\<^esup>)) \<in> Tnodes r s n"
    using node_restrict_node[OF g] m12 m2M by simp
  have 2: "(m2, restrict g ([{0..<m2}]\<^bsup>r\<^esup>)) \<in> Tnodes r s n"
    using node_restrict_node[OF g m2M] .
  have "[{0..<m1}]\<^bsup>r\<^esup> \<subseteq> [{0..<m2}]\<^bsup>r\<^esup>" using m12 by (intro nsets_interval_mono) simp
  hence "\<forall>x \<in> [{0..<m1}]\<^bsup>r\<^esup>.
           restrict g ([{0..<m2}]\<^bsup>r\<^esup>) x = restrict g ([{0..<m1}]\<^bsup>r\<^esup>) x" by auto
  thus ?thesis using 1 2 m12 by (simp add: Rext_iff)
qed

lemma Rext_restrict_node:
  assumes g: "(M, g) \<in> Tnodes r s n" and mM: "m < M"
  shows "((m, restrict g ([{0..<m}]\<^bsup>r\<^esup>)), (M, g)) \<in> Rext r s n"
  using Rext_restrict[OF g mM order_refl] node_restrict_eq[OF g] by simp

text \<open>The nodes below a node \<open>(M, g)\<close> are exactly the restrictions of \<open>g\<close> to
  the levels \<open>m < M\<close>; in particular the node \<open>(M, g)\<close> has height \<open>M\<close>.\<close>

lemma predecessors_node:
  assumes g: "(M, g) \<in> Tnodes r s n"
  shows "predecessors (Tnodes r s n) (M, g) (Rext r s n) =
           (\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}"
proof
  show "predecessors (Tnodes r s n) (M, g) (Rext r s n) \<subseteq>
          (\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}"
  proof
    fix p
    assume "p \<in> predecessors (Tnodes r s n) (M, g) (Rext r s n)"
    hence p: "(p, (M, g)) \<in> Rext r s n" by (simp add: predecessors_def)
    obtain m f where pmf: "p = (m, f)" by (cases p) auto
    have mf: "(m, f) \<in> Tnodes r s n" and mM: "m < M"
      and agree: "\<forall>x \<in> [{0..<m}]\<^bsup>r\<^esup>. g x = f x"
      using p pmf by (simp_all add: Rext_iff)
    have "f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}" using mf by (simp add: Tnodes_def)
    moreover have "restrict g ([{0..<m}]\<^bsup>r\<^esup>) \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}"
      using node_restrict_node[OF g, of m] mM by (simp add: Tnodes_def)
    ultimately have "f = restrict g ([{0..<m}]\<^bsup>r\<^esup>)"
      using agree by (intro PiE_ext) auto
    thus "p \<in> (\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}" using pmf mM by auto
  qed
next
  show "(\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M} \<subseteq>
          predecessors (Tnodes r s n) (M, g) (Rext r s n)"
  proof
    fix p
    assume "p \<in> (\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}"
    then obtain m where mM: "m < M" and pm: "p = (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))" by auto
    have "p \<in> Tnodes r s n" using node_restrict_node[OF g, of m] mM pm by simp
    moreover have "(p, (M, g)) \<in> Rext r s n" using Rext_restrict_node[OF g mM] pm by simp
    ultimately show "p \<in> predecessors (Tnodes r s n) (M, g) (Rext r s n)"
      by (simp add: predecessors_def)
  qed
qed

lemma height_node:
  assumes g: "(M, g) \<in> Tnodes r s n"
  shows "height (Tnodes r s n) (M, g) (Rext r s n) = M"
proof -
  have "inj_on (\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) {..<M}" by (rule inj_onI) simp
  hence "card ((\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}) = M"
    by (simp add: card_image)
  thus ?thesis using predecessors_node[OF g] by (simp add: height_def)
qed

lemma total_predecessors_node:
  assumes g: "(M, g) \<in> Tnodes r s n"
  shows "total_on (predecessors (Tnodes r s n) (M, g) (Rext r s n)) (Rext r s n)"
proof -
  let ?P = "(\<lambda>m. (m, restrict g ([{0..<m}]\<^bsup>r\<^esup>))) ` {..<M}"
  have "total_on ?P (Rext r s n)"
  proof (unfold total_on_def, intro ballI impI)
    fix p q
    assume "p \<in> ?P" and "q \<in> ?P" and pq: "p \<noteq> q"
    then obtain m1 m2 where m1: "m1 < M" "p = (m1, restrict g ([{0..<m1}]\<^bsup>r\<^esup>))"
      and m2: "m2 < M" "q = (m2, restrict g ([{0..<m2}]\<^bsup>r\<^esup>))" by auto
    have "m1 \<noteq> m2" using pq m1(2) m2(2) by auto
    hence "m1 < m2 \<or> m2 < m1" by arith
    thus "(p, q) \<in> Rext r s n \<or> (q, p) \<in> Rext r s n"
    proof
      assume "m1 < m2"
      hence "(p, q) \<in> Rext r s n" using Rext_restrict[OF g _ less_imp_le[OF m2(1)]] m1(2) m2(2) by simp
      thus ?thesis by simp
    next
      assume "m2 < m1"
      hence "(q, p) \<in> Rext r s n" using Rext_restrict[OF g _ less_imp_le[OF m1(1)]] m1(2) m2(2) by simp
      thus ?thesis by simp
    qed
  qed
  thus ?thesis using predecessors_node[OF g] by simp
qed

lemma Rext_strict_part_order: "strict_part_order (Tnodes r s n) (Rext r s n)"
proof -
  have "irrefl_on (Tnodes r s n) (Rext r s n)"
  proof (unfold irrefl_on_def, intro ballI)
    fix p :: "nat \<times> (nat set \<Rightarrow> nat)"
    obtain m f where "p = (m, f)" by (cases p) auto
    thus "(p, p) \<notin> Rext r s n" by (simp add: Rext_iff)
  qed
  moreover have "trans_on (Tnodes r s n) (Rext r s n)"
  proof (unfold trans_on_def, intro ballI impI)
    fix p q t
    assume pq: "(p, q) \<in> Rext r s n" and qt: "(q, t) \<in> Rext r s n"
    obtain m1 f1 where p: "p = (m1, f1)" by (cases p) auto
    obtain m2 f2 where q: "q = (m2, f2)" by (cases q) auto
    obtain m3 f3 where t: "t = (m3, f3)" by (cases t) auto
    have h: "(m1, f1) \<in> Tnodes r s n" "(m3, f3) \<in> Tnodes r s n" "m1 < m2" "m2 < m3"
      "\<forall>x \<in> [{0..<m1}]\<^bsup>r\<^esup>. f2 x = f1 x" "\<forall>x \<in> [{0..<m2}]\<^bsup>r\<^esup>. f3 x = f2 x"
      using pq qt p q t by (simp_all add: Rext_iff)
    have "[{0..<m1}]\<^bsup>r\<^esup> \<subseteq> [{0..<m2}]\<^bsup>r\<^esup>" using h(3) by (intro nsets_interval_mono) simp
    hence "\<forall>x \<in> [{0..<m1}]\<^bsup>r\<^esup>. f3 x = f1 x" using h(5,6) by auto
    thus "(p, t) \<in> Rext r s n" using h p t by (simp add: Rext_iff)
  qed
  ultimately show ?thesis by (simp add: strict_part_order_def)
qed

text \<open>There are only finitely many functions from a given finite set to a given
  finite set, so the nodes up to any given level form a finite set; in
  particular the tree is finitely branching and its set of nodes is countable.\<close>

lemma finite_Tnodes_bounded: "finite {p \<in> Tnodes r s n. fst p < M}"
proof (rule finite_subset)
  show "{p \<in> Tnodes r s n. fst p < M} \<subseteq> (SIGMA m:{..<M}. [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
    by (auto simp: Tnodes_def)
  show "finite (SIGMA m:{..<M}. [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
    by (intro finite_SigmaI finite_PiE finite_imp_finite_nsets) auto
qed

lemma countable_Tnodes: "countable (Tnodes r s n)"
proof (rule countable_subset)
  show "Tnodes r s n \<subseteq> (SIGMA m:(UNIV::nat set). [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
    by (auto simp: Tnodes_def)
  show "countable (SIGMA m:(UNIV::nat set). [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
  proof (rule countable_SIGMA)
    show "countable (UNIV :: nat set)" by simp
  next
    fix m :: nat
    show "countable ([{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
      by (intro countable_finite finite_PiE finite_imp_finite_nsets) auto
  qed
qed

lemma imm_successors_node:
  assumes f: "(m, f) \<in> Tnodes r s n"
  shows "imm_successors (Tnodes r s n) (m, f) (Rext r s n) \<subseteq>
           {Suc m} \<times> ([{0..<Suc m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
proof
  fix p
  assume "p \<in> imm_successors (Tnodes r s n) (m, f) (Rext r s n)"
  hence p: "p \<in> Tnodes r s n"
    "height (Tnodes r s n) p (Rext r s n) = height (Tnodes r s n) (m, f) (Rext r s n) + 1"
    by (simp_all add: imm_successors_def)
  obtain m' g where pg: "p = (m', g)" by (cases p) auto
  have g: "(m', g) \<in> Tnodes r s n" using p(1) pg by simp
  have "m' = Suc m" using p(2) pg height_node[OF g] height_node[OF f] by simp
  moreover have "g \<in> [{0..<m'}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}" using g by (simp add: Tnodes_def)
  ultimately show "p \<in> {Suc m} \<times> ([{0..<Suc m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})" using pg by simp
qed

lemma finitely_branching_Tnodes: "finitely_branching (Tnodes r s n) (Rext r s n)"
proof (unfold finitely_branching_def, intro ballI)
  fix p
  assume p: "p \<in> Tnodes r s n"
  obtain m f where pmf: "p = (m, f)" by (cases p) auto
  have "imm_successors (Tnodes r s n) p (Rext r s n) \<subseteq>
          {Suc m} \<times> ([{0..<Suc m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s})"
    using imm_successors_node[of m f] p pmf by simp
  moreover have "finite ({Suc m} \<times> ([{0..<Suc m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}))"
    by (intro finite_cartesian_product finite_PiE finite_imp_finite_nsets) auto
  ultimately show "finite (imm_successors (Tnodes r s n) p (Rext r s n))"
    by (rule finite_subset)
qed


subsection \<open>The tree when Theorem 26.1 fails\<close>

text \<open>Assume that Theorem 26.1 fails for \<open>r, s, n\<close>: for every \<open>m \<ge> n\<close> there
  exists a partition \<open>f : [{0,\<dots>,m-1}]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close> having no size-\<open>n\<close>
  homogeneous set.  Then every level of the tree is nonempty, and what we have
  defined is an infinite tree.\<close>

context
  fixes r s n :: nat
  assumes r: "0 < r"
    and fails: "\<forall>m \<ge> n. \<exists>f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow> {1..s}.
                  \<not> (\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r f Y)"
begin

lemma level_nonempty: "\<exists>f. (m, f) \<in> Tnodes r s n"
proof -
  have "max m n \<ge> n" by simp
  then obtain f where f: "f \<in> [{0..<max m n}]\<^bsup>r\<^esup> \<rightarrow> {1..s}"
    and noh: "\<not> (\<exists>Y \<in> [{0..<max m n}]\<^bsup>n\<^esup>. homogeneous r f Y)"
    using fails by blast
  have "(m, restrict f ([{0..<m}]\<^bsup>r\<^esup>)) \<in> Tnodes r s n"
    using node_restrict[OF f noh] by simp
  thus ?thesis by blast
qed

lemma root_in_Tnodes: "(0, \<lambda>x. undefined) \<in> Tnodes r s n"
proof -
  obtain f where f: "(0, f) \<in> Tnodes r s n" using level_nonempty by blast
  hence "f \<in> [{0..<0}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}" by (simp add: Tnodes_def)
  hence "f = (\<lambda>x. undefined)" using nsets_interval_zero[OF r] by simp
  thus ?thesis using f by simp
qed

lemma root_minimum: "minimum (Tnodes r s n) (0, \<lambda>x. undefined) (Rext r s n)"
proof -
  have "\<forall>p \<in> Tnodes r s n. p \<noteq> (0, \<lambda>x. undefined) \<longrightarrow> ((0, \<lambda>x. undefined), p) \<in> Rext r s n"
  proof (intro ballI impI)
    fix p
    assume p: "p \<in> Tnodes r s n" and ne: "p \<noteq> (0, \<lambda>x. undefined)"
    obtain m g where pmg: "p = (m, g)" by (cases p) auto
    have g: "(m, g) \<in> Tnodes r s n" using p pmg by simp
    have "m \<noteq> 0"
    proof
      assume "m = 0"
      hence "g \<in> [{0..<0}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}" using g by (simp add: Tnodes_def)
      hence "g = (\<lambda>x. undefined)" using nsets_interval_zero[OF r] by simp
      thus False using ne pmg \<open>m = 0\<close> by simp
    qed
    hence "0 < m" by simp
    hence "((0, restrict g ([{0..<0}]\<^bsup>r\<^esup>)), (m, g)) \<in> Rext r s n"
      by (rule Rext_restrict_node[OF g])
    moreover have "restrict g ([{0..<0}]\<^bsup>r\<^esup>) = (\<lambda>x. undefined)"
      using nsets_interval_zero[OF r] by (simp add: restrict_def)
    ultimately show "((0, \<lambda>x. undefined), p) \<in> Rext r s n" using pmg by simp
  qed
  thus ?thesis using root_in_Tnodes by (simp add: minimum_def)
qed

lemma tree_Tnodes: "tree (Tnodes r s n) (Rext r s n)"
proof (unfold tree_def, intro conjI)
  show "Rext r s n \<subseteq> Tnodes r s n \<times> Tnodes r s n"
    by (auto simp: Rext_def)
next
  obtain f where f: "(1, f) \<in> Tnodes r s n" using level_nonempty by blast
  hence "((0, \<lambda>x. undefined), (1, f)) \<in> Rext r s n"
    using root_minimum by (simp add: minimum_def)
  thus "Rext r s n \<noteq> {}" by blast
next
  show "strict_part_order (Tnodes r s n) (Rext r s n)" by (rule Rext_strict_part_order)
next
  show "\<exists>a. minimum (Tnodes r s n) a (Rext r s n)" using root_minimum by blast
next
  show "\<forall>a \<in> Tnodes r s n. finite (predecessors (Tnodes r s n) a (Rext r s n)) \<and>
          total_on (predecessors (Tnodes r s n) a (Rext r s n)) (Rext r s n)"
  proof
    fix a
    assume a: "a \<in> Tnodes r s n"
    obtain M g where aMg: "a = (M, g)" by (cases a) auto
    have g: "(M, g) \<in> Tnodes r s n" using a aMg by simp
    show "finite (predecessors (Tnodes r s n) a (Rext r s n)) \<and>
          total_on (predecessors (Tnodes r s n) a (Rext r s n)) (Rext r s n)"
      using predecessors_node[OF g] total_predecessors_node[OF g] aMg by simp
  qed
qed

lemma infinite_Tnodes: "infinite (Tnodes r s n)"
proof
  assume "finite (Tnodes r s n)"
  hence "finite (fst ` Tnodes r s n)" by simp
  moreover have "fst ` Tnodes r s n = \<omega>"
  proof (rule set_eqI)
    fix m :: nat
    obtain f where "(m, f) \<in> Tnodes r s n" using level_nonempty by blast
    hence "m \<in> fst ` Tnodes r s n" by force
    thus "m \<in> fst ` Tnodes r s n \<longleftrightarrow> m \<in> \<omega>" by simp
  qed
  ultimately show False by simp
qed

end


subsection \<open>Theorem 26.1 (Ramsey's theorem)\<close>

text \<open>For all \<open>r, s > 0\<close> and every \<open>n\<close> there is an \<open>m \<ge> n\<close> such that every
  partition of \<open>[{0,\<dots>,m-1}]\<^bsup>r\<^esup>\<close> into \<open>s\<close> classes has a size-\<open>n\<close> homogeneous
  set.  No condition relating \<open>n\<close> and \<open>r\<close> is needed: when \<open>n < r\<close> a size-\<open>n\<close>
  set has no size-\<open>r\<close> subsets, so it is trivially homogeneous.\<close>

theorem Ramsey_Theorem:
  fixes r s n :: nat
  assumes r: "0 < r" and s: "0 < s"
  shows "\<exists>m \<ge> n. \<forall>f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow> {1..s}. \<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r f Y"
proof (rule ccontr)
  txt \<open>Suppose that Theorem 26.1 fails.  Then for every \<open>m \<ge> n\<close> there exists
    a partition \<open>f : [{0,\<dots>,m-1}]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close> having no size-\<open>n\<close>
    homogeneous set \<open>Y\<close>.\<close>
  assume "\<not> ?thesis"
  hence fails: "\<forall>m \<ge> n. \<exists>f \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow> {1..s}.
                  \<not> (\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r f Y)"
    by blast
  txt \<open>Let \<open>T\<close> be the set of all such partitions without size-\<open>n\<close> homogeneous
    sets, ordered by extension.  What we have defined is a tree, with finitely
    many nodes in each level, and infinite.\<close>
  let ?T = "Tnodes r s n" and ?R = "Rext r s n"
  have "tree ?T ?R" using tree_Tnodes[OF r fails] .
  moreover have "countable ?T" by (rule countable_Tnodes)
  moreover have "infinite ?T" using infinite_Tnodes[OF r fails] .
  moreover have "finitely_branching ?T ?R" by (rule finitely_branching_Tnodes)
  txt \<open>König's lemma then tells us there will be an infinite branch, that is,
    an infinite set \<open>B\<close> of partitions, each one extending the ones below it,
    none of them having a size-\<open>n\<close> homogeneous set.  This is the step of the
    proof that depends on the compactness theorem.\<close>
  ultimately obtain B where B: "infinite_path B ?T ?R"
    using Koenig_Lemma_countable by blast
  hence BT: "B \<subseteq> ?T" and Btot: "total_on B ?R" and Binf: "infinite B"
    by (auto simp: infinite_path_def path_def sub_linear_order_def)
  txt \<open>Since every level of the tree is finite, the branch contains partitions
    of arbitrarily large levels.\<close>
  have high: "\<exists>m g. (m, g) \<in> B \<and> M \<le> m" for M
  proof (rule ccontr)
    assume low: "\<not> (\<exists>m g. (m, g) \<in> B \<and> M \<le> m)"
    have "B \<subseteq> {p \<in> ?T. fst p < M}"
    proof
      fix p
      assume p: "p \<in> B"
      obtain m g where pmg: "p = (m, g)" by (cases p) auto
      have "m < M" using low p pmg by auto
      thus "p \<in> {p \<in> ?T. fst p < M}" using p pmg BT by auto
    qed
    hence "finite B" using finite_Tnodes_bounded finite_subset by blast
    thus False using Binf by contradiction
  qed
  txt \<open>Any two partitions of the branch assign the same value to any argument
    in both domains, since one of them extends the other.\<close>
  have agree: "g1 x = g2 x"
    if "(m1, g1) \<in> B" "(m2, g2) \<in> B" "x \<in> [{0..<m1}]\<^bsup>r\<^esup>" "x \<in> [{0..<m2}]\<^bsup>r\<^esup>"
    for m1 g1 m2 g2 x
  proof (cases "(m1, g1) = (m2, g2)")
    case True
    thus ?thesis by simp
  next
    case False
    hence "((m1, g1), (m2, g2)) \<in> ?R \<or> ((m2, g2), (m1, g1)) \<in> ?R"
      using Btot that(1,2) unfolding total_on_def by blast
    thus ?thesis using that(3,4) by (auto simp: Rext_iff)
  qed
  txt \<open>We can then define a partition \<open>F : [\<omega>]\<^bsup>r\<^esup> \<rightarrow> {1,\<dots>,s}\<close> as follows: for
    any size-\<open>r\<close> subset \<open>x\<close> of \<open>\<omega>\<close>, \<open>F(x)\<close> is the common value \<open>g(x)\<close> of the
    partitions \<open>g\<close> of the branch whose domain contains \<open>x\<close>.\<close>
  define F where "F = (\<lambda>x. snd (SOME p. p \<in> B \<and> x \<in> [{0..<fst p}]\<^bsup>r\<^esup>) x)"
  have F_eq: "F x = g x" if "(m, g) \<in> B" "x \<in> [{0..<m}]\<^bsup>r\<^esup>" for m g x
  proof -
    let ?p = "SOME p. p \<in> B \<and> x \<in> [{0..<fst p}]\<^bsup>r\<^esup>"
    have "\<exists>p. p \<in> B \<and> x \<in> [{0..<fst p}]\<^bsup>r\<^esup>" using that by force
    hence p: "?p \<in> B \<and> x \<in> [{0..<fst ?p}]\<^bsup>r\<^esup>" by (rule someI_ex)
    have "snd ?p x = g x" using agree[of "fst ?p" "snd ?p" m g x] p that by simp
    thus ?thesis by (simp add: F_def)
  qed
  have F: "F \<in> [\<omega>]\<^bsup>r\<^esup> \<rightarrow> {1..s}"
  proof (rule Pi_I)
    fix x
    assume x: "x \<in> [\<omega>]\<^bsup>r\<^esup>"
    hence "finite x" by (simp add: nsets_def)
    then obtain M where xM: "x \<subseteq> {..<M}" using finite_nat_bounded by blast
    obtain m g where mg: "(m, g) \<in> B" "M \<le> m" using high by blast
    have xm: "x \<in> [{0..<m}]\<^bsup>r\<^esup>" using x xM mg(2) by (auto simp: nsets_def)
    have "g \<in> [{0..<m}]\<^bsup>r\<^esup> \<rightarrow>\<^sub>E {1..s}" using mg(1) BT by (auto simp: Tnodes_def)
    hence "g x \<in> {1..s}" using xm by (rule PiE_mem)
    thus "F x \<in> {1..s}" using F_eq[OF mg(1) xm] by simp
  qed
  txt \<open>By the infinitary version of Ramsey's theorem, \<open>F\<close> has an infinite
    homogeneous set: there is an infinite \<open>Y\<close> and a \<open>j\<close> with \<open>1 \<le> j \<le> s\<close>
    such that \<open>F : [Y]\<^bsup>r\<^esup> \<rightarrow> {j}\<close>.\<close>
  obtain Y j where Y: "infinite Y" and FY: "F \<in> [Y]\<^bsup>r\<^esup> \<rightarrow> {j}"
    using Infinitary_Ramsey_Theorem[OF r s F] by blast
  txt \<open>Let \<open>Z\<close> be a set of \<open>n\<close> elements of \<open>Y\<close> (the book takes the first \<open>n\<close>
    elements of \<open>Y\<close>; any \<open>n\<close> of them will do), and take a partition \<open>g\<close> of the
    branch at a level \<open>m\<close> large enough that \<open>Z \<subseteq> {0,\<dots>,m-1}\<close>.\<close>
  obtain Z where Z: "Z \<subseteq> Y" "finite Z" "card Z = n"
    using infinite_arbitrarily_large[OF Y] by blast
  obtain M where ZM: "Z \<subseteq> {..<M}" using finite_nat_bounded[OF Z(2)] by blast
  obtain m g where mg: "(m, g) \<in> B" "M \<le> m" using high by blast
  have Zm: "Z \<in> [{0..<m}]\<^bsup>n\<^esup>" using Z ZM mg(2) by (auto simp: nsets_def)
  txt \<open>Then \<open>Z\<close> is a size-\<open>n\<close> subset of \<open>{0,\<dots>,m-1}\<close> with \<open>g(x) = F(x) = j\<close> for
    all size-\<open>r\<close> subsets \<open>x\<close> of \<open>Z\<close>.  In other words, \<open>Z\<close> is a size-\<open>n\<close>
    homogeneous set for \<open>g\<close>,\<close>
  have "g \<in> [Z]\<^bsup>r\<^esup> \<rightarrow> {j}"
  proof (rule Pi_I)
    fix x
    assume x: "x \<in> [Z]\<^bsup>r\<^esup>"
    have "x \<in> [Y]\<^bsup>r\<^esup>" using x Z(1) nsets_mono by blast
    hence "F x \<in> {j}" using FY by (rule funcset_mem[rotated])
    moreover have "x \<in> [{0..<m}]\<^bsup>r\<^esup>" using x Zm by (auto simp: nsets_def)
    hence "F x = g x" using F_eq[OF mg(1)] by blast
    ultimately show "g x \<in> {j}" by simp
  qed
  hence "\<exists>Y \<in> [{0..<m}]\<^bsup>n\<^esup>. homogeneous r g Y" using Zm by blast
  txt \<open>which is impossible, since \<open>g\<close> is in \<open>T\<close>.  This contradiction completes
    the proof.\<close>
  moreover have "(m, g) \<in> ?T" using mg(1) BT by blast
  ultimately show False by (simp add: Tnodes_def)
qed

end
