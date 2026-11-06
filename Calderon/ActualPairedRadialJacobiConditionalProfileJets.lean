import Calderon.ActualPairedRadialJacobiThreeJetRoom
import Calderon.ActualRadiusThreeJetProfileRoom
import Calderon.LocalSignedRadiusPowerCompositionJets
import Calderon.ProductIteratedFDerivBounds

/-! Original native 31 jet bounds at any positive amplitude satisfying scalar profile bounds; no amplitude is selected. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic ActualHigherRadiusProfile
  ConformalDepth RadiusProfile ReferenceWeightedApproximation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  ProductIteratedFDerivBounds

local instance referenceConditionalPairedJacobiJetsHalfCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceConditionalPairedJacobiJetsNegativeCompleteSpace :
    CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceConditionalPairedJacobiJetsHighOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  infer_instance

local instance referenceConditionalPairedJacobiJetsLowOperatorCompleteSpace :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by
  infer_instance

attribute [local irreducible] harmonicSphereSubspace referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceRadialEndpointInvertibleLocus secondTaylorRemainder

theorem exists_referencePairedRadialJacobi_scaled_jets_of_profile_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (hg : IsAdmissibleMetric g) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ) :
    let Sh : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Sl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      referenceLowerRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let Th : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Tl : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Nhi : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := fun i j z =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nhalf : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i j z =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nneg : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun i j z =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    ∃ dGeom Cscaled : ℝ, 0 < dGeom ∧ dGeom ≤ ρ ∧ dGeom ≤ 1 ∧
      ((Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dGeom) dGeom)) ⊆
        referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      1 ≤ Cscaled ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ A : ℝ, 0 < A → ∀ p : ℕ, 1 ≤ p → ∀ eta : ℝ, 0 < eta →
      ∀ x ∈ K,
        let beta := actualReferenceBeta g L q delta A p x
        1 ≤ beta → referenceRadius delta A p L x ≤ dGeom →
        referenceRadius delta A p L x * beta^2 ≤ eta →
        ∀ s : ℝ, |s| ≤ 1 → ∀ power : ℕ, 1 ≤ power → power ≤ 3 →
        ∀ order : ℕ, order ≤ 3 →
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Sh (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Sl (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Th (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Tl (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ∀ i j : Fin 3,
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nhi i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nhalf i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) ∧
          ‖iteratedFDeriv ℝ order
            (fun y : R3 => (s * referenceRadius delta A p L y)^power •
              Nneg i j (q,(y,s * referenceRadius delta A p L y))) x‖ ≤
            Cscaled * eta^power * beta^order / beta^(2*power) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "CONDITIONAL_PAIRED_JACOBI BODY_ENTER"
    out.flush
  intro Sh Sl Th Tl Nhi Nhalf Nneg
  let raw := Classical.choice (exists_referencePairedRadialJacobiThreeJetRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg)
  let paired := raw.pairedRoom
  let multipliers := raw.multiplierBounds
  let scalar := Classical.choice (exists_referenceRadiusThreeJetProfileRoom g hg L hL K hK)
  let dGeom : ℝ := paired.radius
  let M : ℝ := max paired.bound multipliers.bound
  let P : ℝ := scalar.radiusJetBound
  let Cscaled : ℝ := 1+6*P^3*M*(P+4)^3
  have hdGeom : 0 < dGeom := paired.radius_pos
  have hdGeomρ : dGeom ≤ ρ := paired.radius_le
  have hdGeom1 : dGeom ≤ 1 := paired.radius_le_one
  have hP : 1 ≤ P := scalar.one_le_radiusJetBound
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPairM : paired.bound ≤ M := le_max_left _ _
  have hJacobiM : multipliers.bound ≤ M := le_max_right _ _
  have hM : 0 ≤ M := zero_le_one.trans (multipliers.one_le_bound.trans hJacobiM)
  have hCscaled : 1 ≤ Cscaled := by
    have hNonneg : 0 ≤ 6*P^3*M*(P+4)^3 := by positivity
    dsimp [Cscaled]
    linarith only [hNonneg]
  have hCscaled0 : 0 ≤ Cscaled := zero_le_one.trans hCscaled
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "CONDITIONAL_PAIRED_JACOBI RAW_READY"
    out.flush
  refine ⟨dGeom,Cscaled,hdGeom,hdGeomρ,hdGeom1,paired.endpointRoom,hCscaled,?_⟩
  intro q hq delta hdelta hdelta1 A hA p hp eta heta x hx beta hbeta hRd hPower
  let Rprof : R3 → ℝ := referenceRadius delta A p L
  have hbeta0 : 0 ≤ beta := zero_le_one.trans hbeta
  have hbetaPos : 0 < beta := zero_lt_one.trans_le hbeta
  have hRpos : 0 < Rprof x := referenceRadius_pos delta A p L x hdelta hA
  have hRsm : ContDiff ℝ ∞ Rprof := by
    have hLog : ContDiff ℝ ∞ (fun y => Real.log (Rprof y)) :=
      contDiff_log_referenceRadius_profile delta A L p hdelta hA
    have hExp : (fun y => Real.exp (Real.log (Rprof y))) = Rprof := by
      funext y
      exact Real.exp_log (referenceRadius_pos delta A p L y hdelta hA)
    exact hExp ▸ Real.contDiff_exp.comp hLog
  have hRJets (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k Rprof x‖ ≤ P * Rprof x * beta^k :=
    scalar.radiusJets q hq delta hdelta hdelta1 A hA p hp x hx k hk
  intro s hs power hpower1 hpower3 order horder
  let rs : R3 → ℝ := fun y => s*Rprof y
  have hrs : ContDiff ℝ ∞ rs := contDiff_const.mul hRsm
  have hrs3 : ContDiffAt ℝ 3 rs x := hrs.contDiffAt.of_le (by simp)
  have hAbs : |rs x| = |s| *Rprof x := by
    dsimp [rs]
    rw [abs_mul,abs_of_pos hRpos]
  have hAbsR : |rs x| ≤ Rprof x := by
    rw [hAbs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hRpos.le
  have hrSmall : |rs x| ≤ 1 := hAbsR.trans (hRd.trans hdGeom1)
  have hrPower : |rs x| *beta^2 ≤ eta :=
    (mul_le_mul_of_nonneg_right hAbsR (sq_nonneg beta)).trans hPower
  have hrsJets (k : ℕ) (hk : k ≤ 3) :
      ‖iteratedFDeriv ℝ k rs x‖ ≤ P * |rs x| * beta^k := by
    have hkSm : ContDiffAt ℝ k Rprof x := hRsm.contDiffAt.of_le (by simp)
    have hScale : iteratedFDeriv ℝ k rs x = s • iteratedFDeriv ℝ k Rprof x := by
      simpa only [rs,smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := s) hkSm)
    rw [hScale,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |s| *(P*Rprof x*beta^k) :=
        mul_le_mul_of_nonneg_left (hRJets k hk) (abs_nonneg s)
      _ = P* |rs x| *beta^k := by rw [hAbs]; ring
  let point : ℝ × (R3 × ℝ) := (q,(x,rs x))
  have hPairPoint : point ∈ Icc (0 : ℝ) 1 ×ˢ
      (closedBall y0 ρ ×ˢ Icc (-paired.radius) paired.radius) :=
    ⟨hq,hKgeom hx,abs_le.mp (hAbsR.trans hRd)⟩
  have hJacobiPoint : point ∈ Icc (0 : ℝ) 1 ×ˢ
      (closedBall y0 ρ ×ˢ Icc (-ρ) ρ) :=
    ⟨hq,hKgeom hx,abs_le.mp ((hAbsR.trans hRd).trans hdGeomρ)⟩
  have hSJoint := paired.primalPairSmooth point hPairPoint
  have hTJoint := paired.adjointPairSmooth point hPairPoint
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "CONDITIONAL_PAIRED_JACOBI SIGNED_READY"
    out.flush
  have hBetaPower : 0 < beta^(2*power) := pow_pos hbetaPos _
  have hRaised : |rs x|^power * beta^(2*power) ≤ eta^power := by
    have h := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (sq_nonneg beta)) hrPower power
    simpa only [mul_pow,← pow_mul] using h
  have hRadiusScale : |rs x|^power ≤ eta^power / beta^(2*power) :=
    (le_div_iff₀ hBetaPower).2 hRaised
  have hScale : Cscaled* |rs x|^power * beta^order ≤
      Cscaled*eta^power*beta^order / beta^(2*power) := by
    calc
      _ = (Cscaled*beta^order)* |rs x|^power := by ring
      _ ≤ (Cscaled*beta^order)*(eta^power / beta^(2*power)) :=
        mul_le_mul_of_nonneg_left hRadiusScale (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]; ring
  have hApply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F : (ℝ × (R3 × ℝ)) → V)
      (hF : ContDiffAt ℝ ∞ F point)
      (hBound : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k F point‖ ≤ M) :
      ‖iteratedFDeriv ℝ order
        (fun y : R3 => (rs y)^power • F (q,(y,rs y))) x‖ ≤
        Cscaled*eta^power*beta^order / beta^(2*power) := by
    have h := norm_iteratedFDeriv_pow_smul_comp_le_of_three_jet_bounds
      rs F q x beta P M hbeta hP hM hrSmall hrs3
        (hF.of_le (by simp : (3 : ℕ∞ω) ≤ ∞)) hrsJets hBound
        power order hpower1 hpower3 horder
    exact h.trans hScale
  have hSh := hApply Sh hSJoint.fst (fun k hk =>
    ((norm_iteratedFDeriv_fst_le (order := k) hSJoint (by simp)).trans
      (paired.primalPairBounds k hk point hPairPoint)).trans hPairM)
  have hSl := hApply Sl hSJoint.snd (fun k hk =>
    ((norm_iteratedFDeriv_snd_le (order := k) hSJoint (by simp)).trans
      (paired.primalPairBounds k hk point hPairPoint)).trans hPairM)
  have hTh := hApply Th hTJoint.fst (fun k hk =>
    ((norm_iteratedFDeriv_fst_le (order := k) hTJoint (by simp)).trans
      (paired.adjointPairBounds k hk point hPairPoint)).trans hPairM)
  have hTl := hApply Tl hTJoint.snd (fun k hk =>
    ((norm_iteratedFDeriv_snd_le (order := k) hTJoint (by simp)).trans
      (paired.adjointPairBounds k hk point hPairPoint)).trans hPairM)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "CONDITIONAL_PAIRED_JACOBI FOUR_REMAINDERS_READY"
    out.flush
  refine ⟨hSh,hSl,hTh,hTl,?_⟩
  intro i j
  have hJJoint := raw.multiplierProductSmooth point hJacobiPoint i j
  have hHigh := hApply (Nhi i j) hJJoint.fst (fun k hk =>
    (multipliers.highBound k hk point hJacobiPoint i j).trans hJacobiM)
  have hHalf := hApply (Nhalf i j) hJJoint.snd.fst (fun k hk =>
    (multipliers.halfBound k hk point hJacobiPoint i j).trans hJacobiM)
  have hNegative := hApply (Nneg i j) hJJoint.snd.snd (fun k hk =>
    (multipliers.negativeBound k hk point hJacobiPoint i j).trans hJacobiM)
  exact ⟨hHigh,hHalf,hNegative⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
