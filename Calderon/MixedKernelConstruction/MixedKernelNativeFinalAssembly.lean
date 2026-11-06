import Calderon.MixedKernelConstruction.MixedKernelNativeReachedLevel
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- Two actual product solutions agreeing on their ENTIRE overlap glue on their explicit open union. -/
theorem exists_product_solution_on_union_of_eqOn
    (S : KnownSideSourceData) (L lam : ℝ) (U V : Set (R3 × R3)) (hU : IsOpen U) (hV : IsOpen V)
    (F G : R3 × R3 → ℝ) (hF : ProductSolutionOn S L lam F U) (hG : ProductSolutionOn S L lam G V)
    (hEq : EqOn F G (U ∩ V)) :
    ∃ H : R3 × R3 → ℝ, ProductSolutionOn S L lam H (U ∪ V) ∧ EqOn H F U ∧ EqOn H G V := by
  let A : Bool → Set (R3 × R3) := fun b => if b then V else U
  let K : Bool → R3 × R3 → ℝ := fun b => if b then G else F
  have hA : ∀ b, IsOpen (A b) := by intro b;cases b <;> assumption
  have hK : ∀ b, ProductSolutionOn S L lam (K b) (A b) := by intro b;cases b <;> assumption
  have hCompat : ∀ b c, EqOn (K b) (K c) (A b ∩ A c) := by
    intro b c
    cases b <;> cases c
    · exact fun q hq => rfl
    · exact hEq
    · exact fun q hq => (hEq ⟨hq.2,hq.1⟩).symm
    · exact fun q hq => rfl
  obtain ⟨H,hH,hAll⟩ := exists_productSolutionOn_iUnion S L lam A hA K hK hCompat
  have hUnion : (⋃ b, A b)=U ∪ V := by
    ext q
    constructor
    · intro hq
      obtain ⟨b,hb⟩ := mem_iUnion.mp hq
      cases b with
      | false => exact Or.inl hb
      | true => exact Or.inr hb
    · intro hq
      rcases hq with hu | hv
      · exact mem_iUnion.mpr ⟨false,hu⟩
      · exact mem_iUnion.mpr ⟨true,hv⟩
  refine ⟨H,?_,hAll false,hAll true⟩
  simpa only [hUnion] using hH

/-- GENUINE native and Euclidean outputs assemble the ORIGINAL unchanged ConstructedMixedKernel, with all exact coverage and both full crosses. -/
theorem constructedMixedKernel_of_native_reached
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0<lam)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar bound separation tail : ℝ) (p : ℕ) (hd : 0<delta) (hRs : 0<Rstar) (hSep : 0<separation)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y<R)
    (hNativeSep : ∀ q ∈ nativeNonzeroNormalImage S L C lam R, ‖q.1-q.2‖<separation/2)
    (Hseed : R3 × R3 → ℝ) (hReached : NativeReachedAt S L C lam R Rstar tail p Hseed delta)
    (E : Set (R3 × R3)) (hE : IsOpen E) (hERoom : E ⊆ dilatedOffDiagonal S lam)
    (hInitial : initialCross S lam ⊆ E) (hFar : fixedSeparationSet bound separation ⊆ E)
    (HE : R3 × R3 → ℝ) (hESol : ProductSolutionOn S L lam HE E)
    (hE1 : ∀ q ∈ E, lam • q.2 ∈ S.W → HE q=dilatedKernel1 S lam q)
    (hE2 : ∀ q ∈ E, lam • q.1 ∈ S.W → HE q=dilatedKernel2 S lam q) :
    Nonempty (ConstructedMixedKernel S L lam delta Rstar bound separation p C) := by
  obtain ⟨N,HN,hN,hNSource,hSeed,hOutside,hFront,hNSol,hNEq,hN1,hN2⟩ := hReached
  let V : Set (R3 × R3) := initialCross S lam ∪ (E ∩ {q | separation/2<‖q.1-q.2‖})
  have hDOpen : IsOpen (dilatedOffDiagonal S lam) :=
    (S.coordinateRoom_open.preimage ((continuous_const_smul lam).comp continuous_fst)).inter
      ((S.coordinateRoom_open.preimage ((continuous_const_smul lam).comp continuous_snd)).inter
        (isOpen_ne_fun continuous_fst continuous_snd))
  have hInitialOpen : IsOpen (initialCross S lam) := hDOpen.inter
    ((S.W_open.preimage ((continuous_const_smul lam).comp continuous_fst)).union
      (S.W_open.preimage ((continuous_const_smul lam).comp continuous_snd)))
  have hV : IsOpen V := hInitialOpen.union
    (hE.inter (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm))
  have hVE : V ⊆ E := by
    intro q hq
    rcases hq with hi | he
    · exact hInitial hi
    · exact he.1
  have hNV : EqOn HN HE (N ∩ V) := by
    intro q hq
    rcases hq.2 with hi | he
    · rcases hi.2 with hx | hy
      · exact (hN2 q hq.1 hx).trans (hE2 q (hInitial hi) hx).symm
      · exact (hN1 q hq.1 hy).trans (hE1 q (hInitial hi) hy).symm
    · exact False.elim (not_lt_of_ge (hNativeSep q (hNSource hq.1)).le he.2)
  obtain ⟨H,hHSol,hHN,hHE⟩ := exists_product_solution_on_union_of_eqOn S L lam N V hN hV HN HE
    hNSol (productSolutionOn_mono hESol hVE) hNV
  have hNRoom : N ⊆ dilatedOffDiagonal S lam := by
    intro q hq
    have hs := hNSource hq
    exact nativeNormalImage_mem_dilatedOffDiagonal_of_velocity_ne_zero S L C lam hlam R hR hRoom q hs.1 hs.2
  refine ⟨{
    domain := N ∪ V
    domain_open := hN.union hV
    domain_room := ?_
    kernel := H
    product_solution := hHSol
    sphere_cover := ?_
    fixed_separation_cover := ?_
    first_lower_cross := ?_
    second_lower_cross := ?_ }⟩
  · intro q hq
    rcases hq with hn | hv
    · exact hNRoom hn
    · exact hERoom (hVE hv)
  · intro i y hy z hz
    exact Or.inl (hFront (packet_referenceRadius_pair_mem_nativeSphereFront S L C lam hlam
      delta Rstar p hd hRs i y hy z hz ((hRadius y hy.1).trans hRoom)))
  · intro q hq
    have hqSep : separation/2<‖q.1-q.2‖ := by
      have hh := hq.2.2
      linarith only [hh,hSep]
    exact Or.inr (Or.inr ⟨hFar hq,hqSep⟩)
  · intro q hq hqW
    rcases hq with hn | hv
    · exact (hHN hn).trans (hN1 q hn hqW)
    · exact (hHE hv).trans (hE1 q (hVE hv) hqW)
  · intro q hq hqW
    rcases hq with hn | hv
    · exact (hHN hn).trans (hN2 q hn hqW)
    · exact (hHE hv).trans (hE2 q (hVE hv) hqW)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
