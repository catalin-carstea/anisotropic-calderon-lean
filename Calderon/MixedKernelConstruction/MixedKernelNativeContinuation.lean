import Calderon.MixedKernelConstruction.MixedKernelNativeLimitGluing
import Calderon.MixedKernelConstruction.MixedKernelNativeWholeFrontExtension
import Calderon.MixedKernelConstruction.MixedKernelNativeRadialLevelGeometry
import Calderon.MixedKernelConstruction.MixedKernelNativeRadiusLevelPassing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology

/-- One reached ACTUAL full-front collar reaches a smaller original level with the SAME genuine kernel and BOTH full crosses. -/
theorem native_reached_lower_step
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (lo c Rstar tail : ℝ) (p : ℕ) (hlo : 0<lo) (hloc : lo<c) (hRs : 0<Rstar)
    (Hseed : R3 × R3 → ℝ)
    (hRadius : ∀ b ∈ Icc lo c, ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (h : NativeReachedAt S L C lam R Rstar tail p Hseed c) :
    ∃ b ∈ Icc lo c, b<c ∧ NativeReachedAt S L C lam R Rstar tail p Hseed b := by
  obtain ⟨U,H,hU,hSource,hSeed,hOutside,hFront,hSol,hEq,h1,h2⟩ := h
  have hc : 0<c := hlo.trans hloc
  obtain ⟨V,hV,hBase,w,hw,hTarget,hSlab⟩ := exists_native_whole_front_actual_slab S L C lam hlam R hR hRoom
    c Rstar p hc hRs (hRadius c ⟨hloc.le,le_rfl⟩) U hU hFront
  obtain ⟨eta,hEta,hEtaC,Hclose⟩ := exists_uniform_referenceRadius_delta_neighborhood L c Rstar p hc hRs w hw
  let step := min (eta/2) ((c-lo)/2)
  have hStep : 0<step := lt_min (by linarith) (by linarith)
  have hStepEta : step<eta := (min_le_left _ _).trans_lt (by linarith)
  have hStepLo : step≤(c-lo)/2 := min_le_right _ _
  let b := c-step
  have hbLo : lo≤b := by dsimp only [b];linarith only [hStepLo,hloc]
  have hbC : b<c := by dsimp only [b];linarith only [hStep]
  have hb : 0<b := hlo.trans_le hbLo
  have hbI : b ∈ Ioo (c-eta) (c+eta) := by
    dsimp only [b]
    exact ⟨by linarith only [hStepEta],by linarith only [hStep,hEta]⟩
  have hClose := (Hclose b hbI).2
  have hNew := native_new_level_covered_of_actual_slab S L C lam hlam R hR hRoom
    b c Rstar p hb hc hbC.le hRs (hRadius b ⟨hbLo,hbC.le⟩) w hw hClose U hOutside V hBase hSlab
  refine ⟨b,⟨hbLo,hbC.le⟩,hbC,U,H,hU,hSource,hSeed,
    fun q hq => hNew (Or.inl hq),fun q hq => hNew (Or.inr hq),hSol,hEq,h1,h2⟩

/-- Actual same-seed UCP gluing, whole-front PDE extension and the literal radius shell reach EVERY original level. -/
theorem native_reached_all_levels_of_actual_strictness
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling) (hlamPos : 0<lam)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (lo Rstar tail : ℝ) (p : ℕ) (hlo : 0<lo) (hlo1 : lo≤1) (hRs : 0<Rstar) (htail : tail<R)
    (hRadius : ∀ b ∈ Icc lo (1 : ℝ), ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (hTail : ∀ y ∈ cylinder, tail<referenceRadius 1 Rstar p L y)
    (hBoundary : ∀ b ∈ Icc lo (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail)
    (hStrict : ∀ b ∈ Icc lo (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam b Rstar p,
      ProductHessianStrictAt (fun x => S.g1 (lam • x)) (fun y => S.g2 (lam • y))
        q.1 q.2 (nativeGlobalEnergy S L C lam R b Rstar p))
    (Hseed : R3 × R3 → ℝ)
    (hSeedSol : ProductSolutionOn S L lam Hseed (nativeRadialSeedRoom S L C lam R tail))
    (hSeed1 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.2 ∈ S.W → Hseed q=dilatedKernel1 S lam q)
    (hSeed2 : ∀ q ∈ nativeRadialSeedRoom S L C lam R tail,
      lam • q.1 ∈ S.W → Hseed q=dilatedKernel2 S lam q) :
    ∀ a ∈ Icc lo (1 : ℝ), NativeReachedAt S L C lam R Rstar tail p Hseed a := by
  let P : ℝ → Prop := NativeReachedAt S L C lam R Rstar tail p Hseed
  have hTop : P 1 := native_reached_one S L C lam hlam R hR hRoom Rstar tail p hRs
    (hRadius 1 ⟨hlo1,le_rfl⟩) hTail Hseed hSeedSol hSeed1 hSeed2
  have hUp : ∀ a ∈ Icc lo (1 : ℝ), P a → ∀ b ∈ Icc a (1 : ℝ), P b := by
    intro a ha hPa b hb
    have hbAll : b ∈ Icc lo (1 : ℝ) := ⟨ha.1.trans hb.1,hb.2⟩
    exact native_reached_mono_delta S L C lam hlam R hR hRoom a b Rstar tail p
      (hlo.trans_le ha.1) hb.1 hRs Hseed (hRadius b hbAll) (hBoundary b hbAll) hPa
  have hPass : ∀ c ∈ Icc lo (1 : ℝ), (∀ b ∈ Ioc c (1 : ℝ), P b) →
      P lo ∨ ∃ b ∈ Icc lo (1 : ℝ), b<c ∧ P b := by
    intro c hc hHigh
    have hcPos : 0<c := hlo.trans_le hc.1
    have hOld : ∃ F : R3 × R3 → ℝ,
        ProductSolutionOn S L lam F (nativeRadialCanonicalRoom S L C lam R c Rstar tail p) ∧
        EqOn F Hseed (nativeRadialSeedRoom S L C lam R tail) ∧
        (∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
          lam • q.2 ∈ S.W → F q=dilatedKernel1 S lam q) ∧
        (∀ q ∈ nativeRadialCanonicalRoom S L C lam R c Rstar tail p,
          lam • q.1 ∈ S.W → F q=dilatedKernel2 S lam q) := by
      by_cases hc1 : c=1
      · subst c
        exact native_reached_canonical_solution S L C lam R Rstar tail p Hseed 1 hTop
      · have hcLt : c<1 := lt_of_le_of_ne hc.2 hc1
        exact exists_native_canonical_kernel_at_limit S L C lam hlam R hR hRoom
          c Rstar tail p hcPos hcLt hRs htail Hseed hHigh
    obtain ⟨F,hF,hFEq,hF1,hF2⟩ := hOld
    have hPc : P c := native_reached_of_canonical_solution S L C lam hlam hlamPos R hR hRoom
      c Rstar tail p hcPos hRs (hRadius c hc) (hBoundary c hc) (hStrict c hc)
      Hseed F hF hFEq hF1 hF2
    by_cases hcLo : c=lo
    · exact Or.inl (hcLo ▸ hPc)
    · have hloc : lo<c := lt_of_le_of_ne hc.1 (Ne.symm hcLo)
      obtain ⟨b,hb,hbc,hPb⟩ := native_reached_lower_step S L C lam hlam R hR hRoom
        lo c Rstar tail p hlo hloc hRs Hseed
        (fun b hb' => hRadius b ⟨hb'.1,hb'.2.trans hc.2⟩) hPc
      exact Or.inr ⟨b,⟨hb.1,hb.2.trans hc.2⟩,hbc,hPb⟩
  exact all_levels_of_upward_extension_and_level_passing lo 1 hlo1 P hTop hUp hPass

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
