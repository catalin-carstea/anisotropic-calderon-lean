import Calderon.ActualDegreeGramCancellation
import Calderon.ActualHigherSZeroCoefficientBounds
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramBaseDerivative
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualRetainedGeneratorMultiplierGains ActualGeneratorRadialGainedRows
  ActualCanonicalGeneratorAngularGainedRows ActualGeneratorEHighGainedGraph
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier SmoothMetricFrame MovingFrameConnection
  ActualGeneratorEPairedGainedEndpoints ActualFiniteHarmonicCore SphereHarmonic.DegreeGraphLifting
  ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift ReferenceDensityBounds ConformalDepth
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def gramHighNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramHighModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def gramLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def gramLowModule : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] gramHighNormed gramHighModule gramLowNormed gramLowModule

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CGE" => generatorEHigh hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "RevRoom" => ActualReverseEHigherLift.ReverseERoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q
local notation "Uin" => ActualHigherSFormation.higherSInput hO hD
local notation "VF" => ActualHigherSFormation.higherSLift hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "VR" => ActualReverseEHigherLift.reverseEHigherLift g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "FD" => ActualHigherSFormation.higherSDoubleHalf hF hO hD g L y0 Φ B ε C ρ H a w hData hg hcalc τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

local notation "GenRoom" => GeneratorEndpointRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CH" => pairedLeftHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BG" => (Sum.inr () : Generator)

section DifferentiatedCompatibility
variable {X E F N : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- Endpoint compatibility differentiates at a closed-set boundary only with
ambient differentiability and unique within differentiation, both explicit. -/
theorem fderiv_compatible_endpoints (I : E →L[ℝ] F) (J : F →L[ℝ] N)
    (A : X → E →L[ℝ] F) (B : X → F →L[ℝ] N)
    (S : Set X) (t : X) (ht : t ∈ S) (hS : UniqueDiffWithinAt ℝ S t)
    (hA : DifferentiableAt ℝ A t) (hB : DifferentiableAt ℝ B t)
    (hCompat : ∀ z ∈ S, ∀ u : E, J (A z u)=B z (I u)) (v : X) (u : E) :
    J (fderiv ℝ A t v u)=fderiv ℝ B t v (I u) := by
  have ha : HasFDerivAt (fun z => A z u) ((fderiv ℝ A t).flip u) t := by
    simpa only [ContinuousLinearMap.comp_zero,zero_add] using
      hA.hasFDerivAt.clm_apply (hasFDerivAt_const u t)
  have hb : HasFDerivAt (fun z => B z (I u)) ((fderiv ℝ B t).flip (I u)) t := by
    simpa only [ContinuousLinearMap.comp_zero,zero_add] using
      hB.hasFDerivAt.clm_apply (hasFDerivAt_const (I u) t)
  have hl : HasFDerivAt (fun z => J (A z u)) (J.comp ((fderiv ℝ A t).flip u)) t :=
    J.hasFDerivAt.comp t ha
  have he : EqOn (fun z => J (A z u)) (fun z => B z (I u)) S :=
    fun z hz => hCompat z hz u
  have hd := hS.eq hl.hasFDerivWithinAt (hb.hasFDerivWithinAt.congr' he ht)
  exact congrArg (fun T : X →L[ℝ] N => T v) hd
end DifferentiatedCompatibility

local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Original common parameter cylinder is uniquely differentiable, including its boundary. -/
theorem uniqueDiffOn_parameter_room (δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) : UniqueDiffOn ℝ (ParamRoom δ) :=
  (uniqueDiffOn_commonRoom y0 ρ hρ hδ).prod
    (uniqueDiffOn_convex (convex_closedBall _ _)
      ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)

/-- Actual joint derivative compatibility on the SAME original Cm/W. -/
theorem actual_fderiv_canonical_compatibility (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (hδ : 0 < δ) (Cm : CRoom hreg δ0 W δ)
    (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (v : Tpar) (u : Hi) :
    JL (fderiv ℝ (EH i) t v u)=fderiv ℝ (EL i) t v (IH u) :=
  fderiv_compatible_endpoints IH JL (EH i) (EL i) (ParamRoom δ) t ht
    (uniqueDiffOn_parameter_room y0 ρ δ hData.1.2.1 hδ t ht)
    ((Cm.germHigh i t ht).differentiableAt (by simp))
    ((Cm.germLow i t ht).differentiableAt (by simp))
    (fun z hz u => Cm.compat i z hz u) v u

/-- Original physical coefficient-derivative row, with full ordered indices. -/
def degreeGramCoefficientDerivative (i j : Fin 3) (t v : Tpar) (u wb : Hi) : ℝ :=
  ⟪KL (fderiv ℝ (EH i) t v u),KL (EH j t wb)⟫_ℝ+
    ⟪KL (EH i t u),KL (fderiv ℝ (EH j) t v wb)⟫_ℝ

attribute [local irreducible] canonicalHigh canonicalLow sphereSobolevInclusionL
  sphereSobolevHalfToSphereL2L degreeGramCoefficientDerivative generatorHigh

/-- Exact low-endpoint representation avoids an extra Hi norm of the degree lift. -/
theorem degree_gram_coefficient_derivative_low (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (hδ : 0 < δ) (Cm : CRoom hreg δ0 W δ)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (v : Tpar) (u z wb : Hi)
    (hb : IH wb=generatorHigh BG z) :
    degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v u wb =
      PP (fderiv ℝ (EH i) t v u) (EL j t (generatorHigh BG z))+
      PP (EH i t u) (fderiv ℝ (EL j) t v (generatorHigh BG z)) := by
  have hValue := (Cm.compat j t ht wb).trans (congrArg (EL j t) hb)
  have hDeriv := (actual_fderiv_canonical_compatibility
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hδ Cm j t ht v wb).trans
    (congrArg (fderiv ℝ (EL j) t v) hb)
  have hP1 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
    (fderiv ℝ (EH i) t v u) (EH j t wb)
  have hP2 := ActualHigherSPhysicalPairing.halfPairing_eq_inner_sphereL2 hO hD
    (EH i t u) (fderiv ℝ (EH j) t v wb)
  unfold degreeGramCoefficientDerivative
  exact congrArg₂ (fun a b : ℝ => a+b)
    (hP1.symm.trans (congrArg (PP (fderiv ℝ (EH i) t v u)) hValue))
    (hP2.symm.trans (congrArg (PP (EH i t u)) hDeriv))

private lemma nested_op_apply_bound {X E F : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : X →L[ℝ] E →L[ℝ] F) (v : X) (u : E) :
    ‖A v u‖ ≤ ‖A‖*‖v‖*‖u‖ :=
  ((A v).le_opNorm u).trans (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg u))

private lemma comp_op_apply_bound {E F N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (A : F →L[ℝ] N) (D : E →L[ℝ] F) (u : E) :
    ‖A (D u)‖ ≤ ‖A‖*(‖D‖*‖u‖) :=
  (A.le_opNorm (D u)).trans (mul_le_mul_of_nonneg_left (D.le_opNorm u) (norm_nonneg A))

private lemma derivative_pairing_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (A : Hi →L[ℝ] Half) (B : Half →L[ℝ] Neg)
    (DA : X →L[ℝ] Hi →L[ℝ] Half) (DB : X →L[ℝ] Half →L[ℝ] Neg)
    (D : Hi →L[ℝ] Half) (v : X) (u z : Hi) :
    |PP (DA v u) (B (D z))+PP (A u) (DB v (D z))| ≤
      (‖DA‖*‖B‖+‖A‖*‖DB‖)*‖D‖*‖v‖*‖u‖*‖z‖ := by
  have h1 : |PP (DA v u) (B (D z))| ≤ (‖DA‖*‖v‖*‖u‖)*(‖B‖*(‖D‖*‖z‖)) :=
    (abs_sphereSobolevDualPairing_le (1/2 : ℝ) (DA v u) (B (D z))).trans
      (mul_le_mul (nested_op_apply_bound DA v u) (comp_op_apply_bound B D z) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (norm_nonneg DA) (norm_nonneg v)) (norm_nonneg u)))
  have hd : ‖DB v (D z)‖ ≤ ‖DB‖*‖v‖*(‖D‖*‖z‖) :=
    (nested_op_apply_bound DB v (D z)).trans
      (mul_le_mul_of_nonneg_left (D.le_opNorm z) (mul_nonneg (norm_nonneg DB) (norm_nonneg v)))
  have h2 : |PP (A u) (DB v (D z))| ≤ (‖A‖*‖u‖)*(‖DB‖*‖v‖*(‖D‖*‖z‖)) :=
    (abs_sphereSobolevDualPairing_le (1/2 : ℝ) (A u) (DB v (D z))).trans
      (mul_le_mul (A.le_opNorm u) hd (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg u)))
  calc
    _ ≤ |PP (DA v u) (B (D z))|+|PP (A u) (DB v (D z))| := abs_add_le _ _
    _ ≤ (‖DA‖*‖v‖*‖u‖)*(‖B‖*(‖D‖*‖z‖))+
        (‖A‖*‖u‖)*(‖DB‖*‖v‖*(‖D‖*‖z‖)) := add_le_add h1 h2
    _ = _ := by ring

/-- Sharp actual coefficient-row bound in the original Hi norm, with no Hi norm of the degree lift. -/
theorem degree_gram_coefficient_derivative_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (hδ : 0 < δ) (Cm : CRoom hreg δ0 W δ)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (v : Tpar) (u z zb : Hi)
    (hb : IH zb=generatorHigh BG z) :
    |degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v u zb| ≤
      (‖fderiv ℝ (EH i) t‖*‖EL j t‖+‖EH i t‖*‖fderiv ℝ (EL j) t‖)*
        ‖generatorHigh BG‖*‖v‖*‖u‖*‖z‖ :=
  (congrArg abs (degree_gram_coefficient_derivative_low
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hδ Cm i j t ht v u z zb hb)).le.trans
    (derivative_pairing_bound (EH i t) (EL j t) (fderiv ℝ (EH i) t) (fderiv ℝ (EL j) t)
      (generatorHigh BG) v u z)

/-- Actual ambient value/first-derivative caps on the SAME common room. -/
theorem exists_actual_canonical_value_first_caps (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : Fin 3, ∀ t ∈ ParamRoom δ,
      ‖EH i t‖ ≤ M ∧ ‖EL i t‖ ≤ M ∧
      ‖fderiv ℝ (EH i) t‖ ≤ M ∧ ‖fderiv ℝ (EL i) t‖ ≤ M := by
  have hKP := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall (0 : R3 →L[ℝ] ℝ) 1)
  have hHighFull := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun i : Fin 3 => EH i) (ParamRoom δ) hKP (fun i t ht => Cm.germHigh i t ht) 1
  rcases hHighFull with ⟨MH,hMH,hHigh⟩
  have hLowFull := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (fun i : Fin 3 => EL i) (ParamRoom δ) hKP (fun i t ht => Cm.germLow i t ht) 1
  rcases hLowFull with ⟨ML,hML,hLow⟩
  refine ⟨MH+ML,add_nonneg hMH hML,?_⟩
  intro i t ht
  have hh0 := hHigh 0 (by norm_num) t ht i
  have hh1 := hHigh 1 (le_refl _) t ht i
  have hl0 := hLow 0 (by norm_num) t ht i
  have hl1 := hLow 1 (le_refl _) t ht i
  rw [norm_iteratedFDeriv_zero] at hh0 hl0
  rw [norm_iteratedFDeriv_one] at hh1 hl1
  exact ⟨hh0.trans (le_add_of_nonneg_right hML),
    hl0.trans (le_add_of_nonneg_left hMH),
    hh1.trans (le_add_of_nonneg_right hML),hl1.trans (le_add_of_nonneg_left hMH)⟩

/-- Uniform coefficient derivative control with the original Hi norms and arbitrary joint direction.
The constant precedes every profile, point, finite input and angular size. -/
theorem exists_actual_degree_gram_coefficient_derivative_bound (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (hδ : 0 < δ) (Cm : CRoom hreg δ0 W δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ v : Tpar, ∀ u z zb : Hi,
      IH zb=generatorHigh BG z →
      |degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v u zb| ≤
        K*‖v‖*‖u‖*‖z‖ := by
  have hCapsFull := exists_actual_canonical_value_first_caps
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
  rcases hCapsFull with ⟨M,hM,hCaps⟩
  refine ⟨(2*M^2)*‖generatorHigh BG‖,mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) (norm_nonneg _),?_⟩
  intro i j t ht v u z zb hb
  have hRaw := degree_gram_coefficient_derivative_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ hδ Cm i j t ht v u z zb hb
  have hi := hCaps i t ht
  have hj := hCaps j t ht
  have hc : ‖fderiv ℝ (EH i) t‖*‖EL j t‖+‖EH i t‖*‖fderiv ℝ (EL j) t‖ ≤ 2*M^2 := by
    calc
      _ ≤ M*M+M*M := add_le_add
        (mul_le_mul hi.2.2.1 hj.2.1 (norm_nonneg (EL j t)) hM)
        (mul_le_mul hi.1 hj.2.2.2 (norm_nonneg (fderiv ℝ (EL j) t)) hM)
      _ = _ := by ring
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (norm_nonneg (generatorHigh BG))) (norm_nonneg v))
      (norm_nonneg u)) (norm_nonneg z))

/-- ANY original W admits the actual coefficient-derivative bound, with its room discharged. -/
theorem exists_retained_degree_gram_coefficient_derivative_bound (hreg : FixedDirichletRegularity)
    (hKernel : UnitBallValueTraceKernel τ0) (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ v : Tpar, ∀ u z zb : Hi,
      IH zb=generatorHigh BG z →
      |degreeGramCoefficientDerivative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t v u zb| ≤
        K*‖v‖*‖u‖*‖z‖ := by
  have hRoomFull := ActualCommonFirstWordQuadraticAdjoint.exists_common_first_word_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  rcases hRoomFull with ⟨δ,Cm⟩
  have hFull := exists_actual_degree_gram_coefficient_derivative_bound
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm.rev.pos Cm
  rcases hFull with ⟨K,hK,hBound⟩
  exact ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,K,hK,hBound⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualDegreeGramBaseDerivative
