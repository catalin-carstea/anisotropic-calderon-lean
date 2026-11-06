import Calderon.ReferencePrimalCommutatorJetsTarget
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalHighInvertibleLocus referenceRadialEndpointInvertibleLocus
  secondTaylorRemainder realHalfOperatorAdjointL sphereSobolevInclusionL

/-- Two applications of the existing ambient all-order compact cap, with a positive
common cap. -/
lemma exists_pos_common_compact_iteratedFDeriv_bound
    {E V W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : E → V) (h : E → W) (q : Set E) (hq : IsCompact q)
    (hf : ∀ x ∈ q, ContDiffAt ℝ ∞ f x) (hh : ∀ x ∈ q, ContDiffAt ℝ ∞ h x) (N : ℕ) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ n : ℕ, n ≤ N → ∀ x ∈ q,
      ‖iteratedFDeriv ℝ n f x‖ ≤ Cg ∧ ‖iteratedFDeriv ℝ n h x‖ ≤ Cg := by
  obtain ⟨C1, hC1, hb1⟩ :=
    OAI.AnisotropicCalderon.DirichletFamily.exists_compact_iteratedFDeriv_bound f q hq hf N
  obtain ⟨C2, _hC2, hb2⟩ :=
    OAI.AnisotropicCalderon.DirichletFamily.exists_compact_iteratedFDeriv_bound h q hq hh N
  have hle : max C1 C2 ≤ max C1 C2 + 1 := le_add_of_nonneg_right zero_le_one
  refine ⟨max C1 C2 + 1, add_pos_of_nonneg_of_pos (hC1.trans (le_max_left _ _)) one_pos, ?_⟩
  intro n hn x hx
  exact ⟨(hb1 n hn x hx).trans ((le_max_left C1 C2).trans hle),
    (hb2 n hn x hx).trans ((le_max_right C1 C2).trans hle)⟩

/-- Ambient smoothness transfers through the fixed bounded linear negative real Half
adjoint. Typed unapplied template: the Neg diamond stays on a closed term. -/
lemma contDiffAt_neg_realHalfOperatorAdjointL_comp
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (G : X → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) (z : X)
    (hG : ContDiffAt ℝ ∞ G z) :
    ContDiffAt ℝ ∞ (fun x => -realHalfOperatorAdjointL (G x)) z := by
  have hAdj : ContDiff ℝ ∞
      (realHalfOperatorAdjointL :
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →
          (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) := by
    have hTemplate := ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (F := SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) (n := ∞)
    try simp only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq] at hTemplate
    exact hTemplate realHalfOperatorAdjointL
  have hAdjNeg : ContDiff ℝ ∞
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        -realHalfOperatorAdjointL A) := hAdj.neg
  exact hAdjNeg.contDiffAt.comp z hG

theorem exists_reference_primal_commutator_uniform_jets
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    radialPrimalCommutatorUniformJetsTarget g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 := by
  classical
  -- Independent inverse room on the larger centre compact, chosen before m,Km,Kt,N.
  have hWitness :=
    exists_reference_commonRadius_extended_center_inverse_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hWitness with ⟨_lam, _Lam, d0, _hlam, hd0, hd0ρ, hRoom⟩
  have hρ : 0 < ρ := hd0.trans_le hd0ρ
  have h32 : ρ ≤ 3*ρ/2 := by linarith
  unfold radialPrimalCommutatorUniformJetsTarget
  refine ⟨min d0 1, lt_min hd0 one_pos, (min_le_left _ _).trans hd0ρ, min_le_right _ _, ?_⟩
  intro m hm Km hKm hmz Kt hKt N GS GN K
  have hGS : ∀ z ∈ K, ContDiffAt ℝ ∞ GS z := by
    rintro ⟨⟨q,y,r⟩,t⟩ hz
    have hz' : (q ∈ Icc (0 : ℝ) 1 ∧ y ∈ closedBall y0 ρ ∧
        r ∈ Icc (-min d0 1) (min d0 1)) ∧ t ∈ Kt := hz
    obtain ⟨⟨hq,hy,hr⟩,_ht⟩ := hz'
    have hr' : |r| ≤ d0 := (abs_le.mpr ⟨hr.1,hr.2⟩).trans (min_le_left _ _)
    have hy' : y ∈ closedBall y0 (3*ρ/2) :=
      closedBall_subset_closedBall h32 hy
    refine contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 m hm Km hKm hmz q y r t ?_
    intro θ hθ
    have hθr : |θ*r| ≤ d0 := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      calc θ*|r| ≤ 1*|r| := mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg r)
        _ = |r| := one_mul _
        _ ≤ d0 := hr'
    exact (hRoom (q,(y,θ*r)) hq hy' hθr).2.2.1
  -- GN is the fixed bounded linear negative real Half adjoint of GS.
  have hGN : ∀ z ∈ K, ContDiffAt ℝ ∞ GN z := fun z hz =>
    contDiffAt_neg_realHalfOperatorAdjointL_comp GS z (hGS z hz)
  have hK : IsCompact K :=
    (isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)).prod hKt
  exact ⟨fun z hz => ⟨hGS z hz, hGN z hz⟩,
    exists_pos_common_compact_iteratedFDeriv_bound GS GN K hK hGS hGN N⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
