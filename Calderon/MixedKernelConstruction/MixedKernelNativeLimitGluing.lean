import Calderon.MixedKernelConstruction.MixedKernelNativeReachedLevel
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- Actual reached kernels at higher levels glue to ONE genuine old-side solution, with SAME seed and BOTH full crosses. -/
theorem exists_native_canonical_kernel_at_limit
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (c Rstar tail : ℝ) (p : ℕ) (hc : 0<c) (hc1 : c<1) (hRs : 0<Rstar) (htail : tail<R)
    (Hseed : R3 × R3 → ℝ)
    (hReached : ∀ b ∈ Ioc c (1 : ℝ), NativeReachedAt S L C lam R Rstar tail p Hseed b) :
    ∃ H : R3 × R3 → ℝ,
      ProductSolutionOn S L lam H (nativeRadialCanonicalRoom S L C lam R c Rstar tail p) ∧
      EqOn H Hseed (nativeRadialSeedRoom S L C lam R tail) ∧
      (∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
        lam • q.2 ∈ S.W → H q=dilatedKernel1 S lam q) ∧
      (∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
        lam • q.1 ∈ S.W → H q=dilatedKernel2 S lam q) := by
  classical
  let I := {b : ℝ // b ∈ Ioc c (1 : ℝ)}
  choose F hF hEq h1 h2 using fun i : I =>
    native_reached_canonical_solution S L C lam R Rstar tail p Hseed i.1 (hReached i.1 i.2)
  let U : I → Set (R3 × R3) := fun i => nativeRadialCanonicalRoom S L C lam R i.1 Rstar tail p
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_nativeRadialCanonicalRoom S L C lam hlam R hR hRoom i.1 Rstar tail p
      (hc.trans i.2.1) hRs
  have hMono (a b : ℝ) (ha : 0<a) (hab : a≤b) :
      nativeRadialCanonicalRoom S L C lam R b Rstar tail p ⊆
        nativeRadialCanonicalRoom S L C lam R a Rstar tail p := by
    intro q hq
    rcases hq with hs | ho
    · exact Or.inl hs
    · exact Or.inr (nativeRadialOutsideRoom_mono_delta S L C lam R a b Rstar p ha hab hRs.le ho)
  have hSeedEq (i j : I) : EqOn (F i) (F j) (nativeRadialSeedRoom S L C lam R tail) :=
    fun q hq => (hEq i hq).trans (hEq j hq).symm
  have hCompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j) := by
    intro i j
    rcases le_total i.1 j.1 with hij | hji
    · have hSub : U j ⊆ U i := hMono i.1 j.1 (hc.trans i.2.1) hij
      have he := native_product_eq_on_radial_canonical_room S L C lam hlam R hR hRoom
        j.1 c Rstar tail p (hc.trans j.2.1) hc hRs htail
        (productSolutionOn_mono (hF i) hSub) (hF j) (hSeedEq i j)
      exact fun q hq => he hq.2
    · have hSub : U i ⊆ U j := hMono j.1 i.1 (hc.trans j.2.1) hji
      have he := native_product_eq_on_radial_canonical_room S L C lam hlam R hR hRoom
        i.1 c Rstar tail p (hc.trans i.2.1) hc hRs htail
        (hF i) (productSolutionOn_mono (hF j) hSub) (hSeedEq i j)
      exact fun q hq => he hq.1
  obtain ⟨H,hH,hAll⟩ := exists_productSolutionOn_iUnion S L lam U hU F hF hCompat
  let top : I := ⟨1,hc1,le_rfl⟩
  have hUnion : (⋃ i, U i)=nativeRadialCanonicalRoom S L C lam R c Rstar tail p := by
    apply subset_antisymm
    · intro q hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      exact hMono c i.1 hc i.2.1.le hi
    · intro q hq
      rcases hq with hs | ho
      · exact mem_iUnion.mpr ⟨top,Or.inl hs⟩
      · have ho' : q ∈ ⋃ b ∈ Ioc c (1 : ℝ), nativeRadialOutsideRoom S L C lam R b Rstar p := by
          rw [←nativeRadialOutsideRoom_eq_iUnion_larger_delta S L C lam R c Rstar p hc hc1 hRs.le]
          exact ho
        obtain ⟨b,hb,hqb⟩ := mem_iUnion₂.mp ho'
        exact mem_iUnion.mpr ⟨⟨b,hb⟩,Or.inr hqb⟩
  have hSol : ProductSolutionOn S L lam H (nativeRadialCanonicalRoom S L C lam R c Rstar tail p) := by
    simpa only [hUnion] using hH
  refine ⟨H,hSol,?_,?_,?_⟩
  · intro q hq
    exact (hAll top (Or.inl hq)).trans (hEq top hq)
  · intro q hq hqW
    have hIn : q ∈ ⋃ i, U i := by rw [hUnion];exact hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hIn
    exact (hAll i hi).trans (h1 i q hi hqW)
  · intro q hq hqW
    have hIn : q ∈ ⋃ i, U i := by rw [hUnion];exact hq
    obtain ⟨i,hi⟩ := mem_iUnion.mp hIn
    exact (hAll i hi).trans (h2 i q hi hqW)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
