import Calderon.MixedKernelConstruction.MixedKernelNativeFinalAssembly
import Calderon.MixedKernelConstruction.MixedKernelNativeParameterAssembly
import Calderon.ActualMixedKernelNativeH3Datum
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- GENUINE native and Euclidean outputs assemble the ORIGINAL unchanged ConstructedMixedKernel, with all exact coverage and both full crosses. -/
theorem exists_constructedMixedKernel_eq_seed_of_native_reached
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0<lam)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar bound separation tail : ℝ) (p : ℕ) (hd : 0<delta) (hRs : 0<Rstar) (hSep : 0<separation)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y<R)
    (hNativeSep : ∀ q ∈ nativeNonzeroNormalImage S L C lam R, ‖q.1-q.2‖<separation/2)
    (Hseed : R3 × R3 → ℝ) (hReached : NativeReachedAt S L C lam R Rstar tail p Hseed delta)
    (E : Set (R3 × R3)) (hE : IsOpen E) (hERoom : E ⊆ dilatedOffDiagonal S lam)
    (hInitial : initialCross S lam ⊆ E) (hFar : fixedSeparationSet bound separation ⊆ E)
    (hESol : ProductSolutionOn S L lam Hseed E)
    (hE1 : ∀ q ∈ E, lam • q.2 ∈ S.W → Hseed q=dilatedKernel1 S lam q)
    (hE2 : ∀ q ∈ E, lam • q.1 ∈ S.W → Hseed q=dilatedKernel2 S lam q) :
    ∃ K : ConstructedMixedKernel S L lam delta Rstar bound separation p C,
      nativeRadialSeedRoom S L C lam R tail ⊆ K.domain ∧
      EqOn K.kernel Hseed (nativeRadialSeedRoom S L C lam R tail) := by
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
  have hNV : EqOn HN Hseed (N ∩ V) := by
    intro q hq
    rcases hq.2 with hi | he
    · rcases hi.2 with hx | hy
      · exact (hN2 q hq.1 hx).trans (hE2 q (hInitial hi) hx).symm
      · exact (hN1 q hq.1 hy).trans (hE1 q (hInitial hi) hy).symm
    · exact False.elim (not_lt_of_ge (hNativeSep q (hNSource hq.1)).le he.2)
  obtain ⟨H,hHSol,hHN,hHE⟩ := exists_product_solution_on_union_of_eqOn S L lam N V hN hV HN Hseed
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
    second_lower_cross := ?_ },?_,?_⟩
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

  · intro q hq
    exact Or.inl (hSeed hq)
  · intro q hq
    exact (hHN (hSeed hq)).trans (hNEq hq)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
