import Calderon.MixedKernelConstruction.MixedKernelChartOverlap
import Mathlib.Topology.Compactness.Compact
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- A true compact base gives one positive output width about its entire level. -/
theorem exists_compact_level_open_slab {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (a : ℝ) {N : Set (X × ℝ)}
    (hN : IsOpen N) (hKN : K ×ˢ {a} ⊆ N) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ eps : ℝ, 0 < eps ∧
      V ×ˢ Ioo (a-eps) (a+eps) ⊆ N := by
  obtain ⟨V,J,hV,hJ,hKV,haJ,hVJ⟩ :=
    generalized_tube_lemma hK isCompact_singleton hN hKN
  obtain ⟨eps,heps,hinterval⟩ := Metric.isOpen_iff.mp hJ a (haJ (mem_singleton a))
  refine ⟨V,hV,hKV,eps,heps,?_⟩
  rintro z ⟨hzV,hzI⟩
  apply hVJ
  refine ⟨hzV,hinterval ?_⟩
  rw [Metric.mem_ball,Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hzI.1],by linarith [hzI.2]⟩

/-- Actual upward closure keeps the seed comparison path inside a complete output box. -/
theorem actual_chart_box_seed_path {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    (B : Set X) (a d : ℝ) (hd : 0 < d)
    (hT : B ×ˢ Ioo (a-d) (a+d) ⊆ e.target) {A : Set (R3 × R3)}
    (hup : ∀ z ∈ A ∩ e.source, ∀ t : ℝ, (e z).2 ≤ t →
      ((e z).1,t) ∈ e.target → e.symm ((e z).1,t) ∈ A)
    (z : R3 × R3)
    (hz : z ∈ (e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))) ∩ A) :
    ∃ h : ℝ, a < h ∧ ((e z).1,h) ∈ e.target ∧
      ContinuousOn (fun t : ℝ => e.symm ((e z).1,t)) (uIcc (e z).2 h) ∧
      e.symm ((e z).1,(e z).2) = z ∧
      MapsTo (fun t : ℝ => e.symm ((e z).1,t)) (uIcc (e z).2 h)
        ((e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))) ∩ A) := by
  let h := max (e z).2 (a+d/2)
  have hstart : (e z).2 ≤ h := le_max_left _ _
  have hah : a < h := (by linarith : a < a+d/2).trans_le (le_max_right _ _)
  have hupper : h < a+d := max_lt hz.1.2.2.2 (by linarith)
  have hcoords : ∀ t ∈ uIcc (e z).2 h,
      ((e z).1,t) ∈ B ×ˢ Ioo (a-d) (a+d) := by
    intro t ht
    rw [uIcc_of_le hstart] at ht
    exact ⟨hz.1.2.1,hz.1.2.2.1.trans_le ht.1,ht.2.trans_lt hupper⟩
  have hline : MapsTo (fun t : ℝ => ((e z).1,t)) (uIcc (e z).2 h) e.target :=
    fun t ht => hT (hcoords t ht)
  refine ⟨h,hah,hline right_mem_uIcc,e.continuousOn_symm.comp
    (continuous_const.prodMk continuous_id).continuousOn hline,?_,?_⟩
  · exact e.left_inv hz.1.1
  · intro t ht
    have htT := hline ht
    have heq := e.right_inv htT
    have htge : (e z).2 ≤ t := by
      rw [uIcc_of_le hstart] at ht
      exact ht.1
    refine ⟨⟨e.map_target htT,?_⟩,hup z ⟨hz.2,hz.1.1⟩ t htge htT⟩
    change e (e.symm ((e z).1,t)) ∈ B ×ˢ Ioo (a-d) (a+d)
    rw [heq]
    exact hcoords t ht

/-- SAME-chart upward geometry retains agreement on the whole original seed overlap. -/
theorem native_product_eq_on_actual_chart_box_seed {X : Type*} [TopologicalSpace X]
    (S : KnownSideSourceData) (L lam : ℝ)
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    (B : Set X) (hB : IsOpen B) (a d : ℝ) (hd : 0 < d)
    (hT : B ×ˢ Ioo (a-d) (a+d) ⊆ e.target)
    {A : Set (R3 × R3)} (hA : IsOpen A)
    (hup : ∀ z ∈ A ∩ e.source, ∀ t : ℝ, (e z).2 ≤ t →
      ((e z).1,t) ∈ e.target → e.symm ((e z).1,t) ∈ A)
    {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F
      (e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))))
    (hG : ProductSolutionOn S L lam G A)
    (heq : ∀ z ∈ (e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))) ∩ A,
      a < (e z).2 → F z = G z) :
    EqOn F G ((e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))) ∩ A) := by
  let V := e.source ∩ e ⁻¹' (B ×ˢ Ioo (a-d) (a+d))
  let Ω := V ∩ A
  have hV : IsOpen V := e.isOpen_inter_preimage (hB.prod isOpen_Ioo)
  have hΩ : IsOpen Ω := hV.inter hA
  let U := Ω ∩ (e.source ∩ e ⁻¹' ((univ : Set X) ×ˢ Ioi a))
  have hU : IsOpen U := hΩ.inter (e.isOpen_inter_preimage (isOpen_univ.prod isOpen_Ioi))
  apply native_product_eq_of_interval_seed S L lam hΩ hU inter_subset_left
    (productSolutionOn_mono hF inter_subset_left)
    (productSolutionOn_mono hG inter_subset_right)
    (fun z hz => heq z hz.1 hz.2.2.2)
  intro z hz
  obtain ⟨h,hah,htarget,hcont,hleft,hinside⟩ := actual_chart_box_seed_path e B a d hd hT hup z hz
  refine ⟨(e z).2,h,(fun t => e.symm ((e z).1,t)),hcont,hleft,hinside,?_⟩
  have ht := hinside right_mem_uIcc
  refine ⟨ht,ht.1.1, trivial,?_⟩
  change a < (e (e.symm ((e z).1,h))).2
  rw [e.right_inv htarget]
  exact hah

/-- Actual local output solutions glue with the ENTIRE original upward-closed seed. -/
theorem exists_native_product_solution_from_common_level_boxes
    {X ι : Type*} [TopologicalSpace X]
    (S : KnownSideSourceData) (L lam : ℝ)
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    (B : ι → Set X) (hB : ∀ i, IsOpen (B i)) (a : ℝ) (d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hT : ∀ i, B i ×ˢ Ioo (a-d i) (a+d i) ⊆ e.target)
    (A : Set (R3 × R3)) (hA : IsOpen A)
    (hup : ∀ z ∈ A ∩ e.source, ∀ t : ℝ, (e z).2 ≤ t →
      ((e z).1,t) ∈ e.target → e.symm ((e z).1,t) ∈ A)
    (G : R3 × R3 → ℝ) (hG : ProductSolutionOn S L lam G A)
    (F : ι → R3 × R3 → ℝ)
    (hF : ∀ i, ProductSolutionOn S L lam (F i)
      (e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))))
    (heq : ∀ i, ∀ z ∈ (e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))),
      a < (e z).2 → F i z = G z) :
    ∃ N : Set (R3 × R3), IsOpen N ∧ A ⊆ N ∧
      (∀ i, e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i)) ⊆ N) ∧
      ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H N ∧ EqOn H G A ∧
        ∀ i, EqOn H (F i) (e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))) := by
  let V : ι → Set (R3 × R3) := fun i =>
    e.source ∩ e ⁻¹' (B i ×ˢ Ioo (a-d i) (a+d i))
  have hV : ∀ i, IsOpen (V i) := fun i => e.isOpen_inter_preimage ((hB i).prod isOpen_Ioo)
  have hseed : ∀ i, EqOn (F i) G (V i ∩ A) := fun i =>
    native_product_eq_on_actual_chart_box_seed S L lam e (B i) (hB i) a (d i)
      (hd i) (hT i) hA hup (hF i) hG (fun z hz hh => heq i z hz.1 hh)
  have hpairs : ∀ i j, EqOn (F i) (F j) (V i ∩ V j) := by
    intro i j
    apply native_product_eq_on_actual_chart_box_overlap S L lam e
      (B i) (B j) (hB i) (hB j) a (d i) (d j) (hd i) (hd j) (hT i) (hT j)
      (F i) (F j)
      (productSolutionOn_mono (hF i) inter_subset_left)
      (productSolutionOn_mono (hF j) inter_subset_right)
    intro z hz hh
    exact (heq i z hz.1 hh).trans (heq j z hz.2 hh).symm
  let U : Option ι → Set (R3 × R3) := fun o => o.elim A V
  let P : Option ι → R3 × R3 → ℝ := fun o => o.elim G F
  have hU : ∀ o, IsOpen (U o) := by
    intro o
    cases o with
    | none => exact hA
    | some i => exact hV i
  have hP : ∀ o, ProductSolutionOn S L lam (P o) (U o) := by
    intro o
    cases o with
    | none => exact hG
    | some i => exact hF i
  have hcompat : ∀ o p, EqOn (P o) (P p) (U o ∩ U p) := by
    intro o p
    cases o with
    | none =>
      cases p with
      | none => exact fun z hz => rfl
      | some i => exact fun z hz => (hseed i ⟨hz.2,hz.1⟩).symm
    | some i =>
      cases p with
      | none => exact hseed i
      | some j => exact hpairs i j
  obtain ⟨H,hH,hall⟩ := exists_productSolutionOn_iUnion S L lam U hU P hP hcompat
  refine ⟨⋃ o, U o,isOpen_iUnion hU,?_,?_,H,hH,hall none,?_⟩
  · exact subset_iUnion U none
  · intro i
    exact subset_iUnion U (some i)
  · intro i
    exact hall (some i)

/-- A compact level in an actual open output domain has one genuine coordinate width. -/
theorem exists_actual_chart_compact_level_slab {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (R3 × R3) (X × ℝ))
    {K : Set X} (hK : IsCompact K) (a : ℝ) {N : Set (R3 × R3)}
    (hN : IsOpen N) (hT : K ×ˢ {a} ⊆ e.target)
    (hlevel : ∀ z ∈ K ×ˢ {a}, e.symm z ∈ N) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∃ eps : ℝ, 0 < eps ∧
      V ×ˢ Ioo (a-eps) (a+eps) ⊆ e.target ∧
      MapsTo e.symm (V ×ˢ Ioo (a-eps) (a+eps)) N := by
  let M := e.target ∩ e.symm ⁻¹' N
  have hM : IsOpen M := e.symm.isOpen_inter_preimage hN
  have hKM : K ×ˢ {a} ⊆ M := fun z hz => ⟨hT hz,hlevel z hz⟩
  obtain ⟨V,hV,hKV,eps,heps,hslab⟩ := exists_compact_level_open_slab hK a hM hKM
  exact ⟨V,hV,hKV,eps,heps,fun z hz => (hslab hz).1,fun z hz => (hslab hz).2⟩

/-- The last-level argument uses reached higher levels; no limiting solution is assumed. -/
theorem all_levels_of_upward_extension_and_level_passing
    (lo hi : ℝ) (hlohi : lo ≤ hi) (P : ℝ → Prop) (htop : P hi)
    (hup : ∀ a ∈ Icc lo hi, P a → ∀ b ∈ Icc a hi, P b)
    (hpass : ∀ c ∈ Icc lo hi, (∀ b ∈ Ioc c hi, P b) →
      P lo ∨ ∃ b ∈ Icc lo hi, b < c ∧ P b) :
    ∀ a ∈ Icc lo hi, P a := by
  let E : Set ℝ := {a | a ∈ Icc lo hi ∧ P a}
  have hEne : E.Nonempty := ⟨hi,⟨hlohi,le_rfl⟩,htop⟩
  have hEbelow : BddBelow E := ⟨lo,fun a ha => ha.1.1⟩
  let c := sInf E
  have hloc : lo ≤ c := le_csInf hEne (fun a ha => ha.1.1)
  have hchi : c ≤ hi := csInf_le hEbelow ⟨⟨hlohi,le_rfl⟩,htop⟩
  have hhigh : ∀ b ∈ Ioc c hi, P b := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := exists_lt_of_csInf_lt hEne hb.1
    exact hup a ha.1 ha.2 b ⟨hab.le,hb.2⟩
  have hbottom : P lo := by
    rcases hpass c ⟨hloc,hchi⟩ hhigh with h | ⟨b,hb,hbc,hPb⟩
    · exact h
    · have hcb : c ≤ b := csInf_le hEbelow ⟨hb,hPb⟩
      exact False.elim (not_lt_of_ge hcb hbc)
  intro a ha
  exact hup lo ⟨le_rfl,hlohi⟩ hbottom a ha

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
