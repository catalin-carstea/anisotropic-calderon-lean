import Calderon.ActualSAdjointSecondNegative
import Calderon.ReferenceWeightedApproximation

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondPointwiseBound
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualGeneratorEPairedGainedEndpoints
  ActualHigherSSecondAdjoint ActualSAdjointSecondNegative ReferenceWeightedApproximation
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift

private lemma smul_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (v : E) (A D : ℝ) (hc : |c| ≤ A) (hv : ‖v‖ ≤ D) (hA : 0 ≤ A) :
    ‖c • v‖ ≤ A*D := by
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hc hv (norm_nonneg v) hA

private lemma map_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (u : E) (M D : ℝ) (hA : ‖A‖ ≤ M) (hu : ‖u‖ ≤ D) (hM : 0 ≤ M) :
    ‖A u‖ ≤ M*D :=
  (A.le_opNorm u).trans (mul_le_mul hA hu (norm_nonneg u) hM)

private lemma norm_three_sum {E : Type*} [NormedAddCommGroup E]
    (f : Fin 3 → E) (A : ℝ) (hf : ∀ i, ‖f i‖ ≤ A) : ‖∑ i : Fin 3, f i‖ ≤ 3*A := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ => hf i)).trans_eq ?_)
  simp only [Fin.sum_univ_three]
  ring

private lemma norm_nine_sum {E : Type*} [NormedAddCommGroup E]
    (f : Fin 3 → Fin 3 → E) (A : ℝ) (hf : ∀ i j, ‖f i j‖ ≤ A) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, f i j‖ ≤ 9*A := by
  have h := norm_three_sum (fun i => ∑ j : Fin 3, f i j) (3*A)
    (fun i => norm_three_sum (f i) A (hf i))
  exact h.trans_eq (by ring)

private lemma norm_add_sub {E : Type*} [NormedAddCommGroup E] (u v w : E) :
    ‖u+v-w‖ ≤ ‖u‖+‖v‖+‖w‖ := by
  have h1 := norm_sub_le (u+v) w
  have h2 := norm_add_le u v
  linarith

private lemma norm_four_add {E : Type*} [NormedAddCommGroup E]
    (u v w z : E) (A : ℝ) (hu : ‖u‖ ≤ A) (hv : ‖v‖ ≤ A) (hw : ‖w‖ ≤ A) (hz : ‖z‖ ≤ A) :
    ‖u+v+w+z‖ ≤ 4*A := by
  have h1 := norm_add_le (u+v+w) z
  have h2 := norm_add_le (u+v) w
  have h3 := norm_add_le u v
  linarith

private lemma density_rows_bound {E : Type*} [NormedAddCommGroup E]
    (row1 row2 extra : Fin 3 → Fin 3 → E) (conn : Fin 3 → Fin 3 → Fin 3 → E)
    (drift : Fin 3 → E) (W : ℝ)
    (h1 : ∀ i j, ‖row1 i j‖ ≤ 4*W) (h2 : ∀ i j, ‖row2 i j‖ ≤ 7*W)
    (hp : ∀ i j, ‖extra i j‖ ≤ W) (hc : ∀ i j k, ‖conn i j k‖ ≤ W)
    (hb : ∀ i, ‖drift i‖ ≤ W) :
    ‖(∑ i : Fin 3, ∑ j : Fin 3,
      (row1 i j+row2 i j+extra i j-∑ k : Fin 3, conn i j k)) + ∑ i : Fin 3, drift i‖ ≤ 138*W := by
  have hRow (i j : Fin 3) :
      ‖row1 i j+row2 i j+extra i j-∑ k : Fin 3, conn i j k‖ ≤ 15*W := by
    have hC := norm_three_sum (conn i j) W (hc i j)
    have hS := norm_sub_le (row1 i j+row2 i j+extra i j) (∑ k : Fin 3, conn i j k)
    have hA := norm_add_le (row1 i j+row2 i j) (extra i j)
    have hB := norm_add_le (row1 i j) (row2 i j)
    have hh1 := h1 i j
    have hh2 := h2 i j
    have hhp := hp i j
    linarith
  have hSum := norm_nine_sum
    (fun i j => row1 i j+row2 i j+extra i j-∑ k : Fin 3, conn i j k) (15*W) hRow
  have hDrift := norm_three_sum drift W hb
  have hAll := norm_add_le
    (∑ i : Fin 3, ∑ j : Fin 3, (row1 i j+row2 i j+extra i j-∑ k : Fin 3, conn i j k))
    (∑ i : Fin 3, drift i)
  linarith

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
  (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
  (F : smoothCompactFiniteSphereCore hO hD) (x : R3)

local notation "eH" => reverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => reverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" => higherSParam L dr Ar p q
local notation "Uin" => higherSInput hO hD F
local notation "rad" => referenceRadius dr Ar p L x
local notation "bet" => actualReferenceBeta g L q dr Ar p x
local notation "Gsum" => ∑ i : Fin 3, ‖IH (fderiv ℝ Uin x (coordinateDirection i))‖
local notation "SN" => secondAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x
local notation "SDN" => secondAdjointDensityNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x

/-- Concrete raw pointwise caps. The pre-profile producer must discharge all fields. -/
structure SecondPointwiseCaps (M : ℝ) : Prop where
  one_le : 1 ≤ M
  density : |referenceDensityFamily g L (q,x)| ≤ M
  density_inv : |(referenceDensityFamily g L (q,x))⁻¹| ≤ M
  principal : ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M
  log_radius : ∀ i : Fin 3, |referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x i| ≤ M*bet
  connection : ∀ i j k : Fin 3, |referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j| ≤ M
  drift : ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M
  density_derivative : ∀ i j k : Fin 3,
    |densityDerivativeCoefficient g L q k (secondCoefficient g g2 L q dr Ar p i j) x| ≤ M*rad^2*bet
  high_inclusion : ‖IH‖ ≤ M
  low_inclusion : ‖JL‖ ≤ M
  high_degree : ‖sphereSobolevShiftedDegreeL (3/2 : ℝ)‖ ≤ M
  low_degree : ‖sphereSobolevShiftedDegreeL (1/2 : ℝ)‖ ≤ M
  low_connection : ∀ i : Fin 3, ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ M
  reverse_high : ∀ i : Fin 3, ‖eH i (Tq x)‖ ≤ M
  reverse_low : ∀ i : Fin 3, ‖eL i (Tq x)‖ ≤ M
  reverse_low_directional : ∀ i j : Fin 3,
    ‖fderiv ℝ (fun z => eL i (Tq z)) x (referenceMetricGramFrame g L (q,x) j)‖ ≤ M
  frame_input : ∀ i : Fin 3,
    ‖IH (fderiv ℝ Uin x (referenceMetricGramFrame g L (q,x) i))‖ ≤ M*Gsum
  reference_input : ∀ i : Fin 3,
    ‖referenceHighWeightedHorizontalAction g L q (referenceRadius dr Ar p L) Uin x i‖ ≤
      M*(Gsum+bet*‖Uin x‖)

local notation "PC" => SecondPointwiseCaps g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x

attribute [local irreducible] reverseEHigh reverseELow sphereSobolevInclusionL
  sphereSobolevShiftedDegreeL referenceHighWeightedHorizontalAction referenceLowerHorizontalAngularL

/-- The full original Second norm bound under explicit concrete pointwise caps.
The separate actual pre-profile producer remains required. -/
theorem secondAdjointNegative_bound_of_caps (M : ℝ) (caps : PC M)
    (hdr : 0 < dr) (hAr : 0 < Ar) (hbet : 1 ≤ bet) :
    ‖SN‖ ≤ 200*M^6*(rad^2*Gsum+rad^2*bet*‖Uin x‖) := by
  let r : ℝ := rad
  let beta : ℝ := bet
  let u : Hi := Uin x
  let m : ℝ := ‖u‖
  let G : ℝ := Gsum
  let V : ℝ := G+beta*m
  let W0 : ℝ := M^5*r^2*V
  let mu : ℝ := referenceDensityFamily g L (q,x)
  let c := secondCoefficient g g2 L q dr Ar p
  let f := referenceRadiusHorizontalLogDerivative g L q (referenceRadius dr Ar p L) x
  let Gamma := fun i j k : Fin 3 => referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j
  let er := fun i : Fin 3 => eH i (Tq x) u
  let D := fun i : Fin 3 => referenceHighWeightedHorizontalAction g L q (referenceRadius dr Ar p L) Uin x i
  let BU := (sphereSobolevShiftedDegreeL (3/2 : ℝ) u : Half)
  let Wr := fun i j : Fin 3 =>
    (eL i (Tq x) (IH (fderiv ℝ Uin x (referenceMetricGramFrame g L (q,x) j))) +
      (fderiv ℝ (fun z => eL i (Tq z)) x (referenceMetricGramFrame g L (q,x) j)) (IH u)) +
    referenceLowerHorizontalAngularL g L q x j (er i) +
    f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans caps.one_le
  have hr : 0 < r := referenceRadius_pos dr Ar p L x hdr hAr
  have hb : 0 ≤ beta := (by norm_num : (0 : ℝ) ≤ 1).trans hbet
  have hm : 0 ≤ m := norm_nonneg u
  have hG : 0 ≤ G := Finset.sum_nonneg (fun i _ => norm_nonneg (IH (fderiv ℝ Uin x (coordinateDirection i))))
  have hV : 0 ≤ V := add_nonneg hG (mul_nonneg hb hm)
  have hGV : G ≤ V := le_add_of_nonneg_right (mul_nonneg hb hm)
  have hbmV : beta*m ≤ V := le_add_of_nonneg_left hG
  have hmV : m ≤ V := by
    calc
      m = m*1 := (mul_one m).symm
      _ ≤ m*beta := mul_le_mul_of_nonneg_left hbet hm
      _ = beta*m := mul_comm _ _
      _ ≤ V := hbmV
  have hStep (n : ℕ) : M^n ≤ M^(n+1) := by
    calc
      M^n = M^n*1 := (mul_one _).symm
      _ ≤ M^n*M := mul_le_mul_of_nonneg_left caps.one_le (pow_nonneg hM n)
      _ = M^(n+1) := (pow_succ M n).symm
  have h23 : M^2 ≤ M^3 := hStep 2
  have h45 : M^4 ≤ M^5 := hStep 4
  have h35 : M^3 ≤ M^5 := (hStep 3).trans h45
  have hG3 : M^2*G ≤ M^3*V :=
    (mul_le_mul_of_nonneg_right h23 hG).trans (mul_le_mul_of_nonneg_left hGV (pow_nonneg hM 3))
  have hm3 : M^2*m ≤ M^3*V :=
    (mul_le_mul_of_nonneg_right h23 hm).trans (mul_le_mul_of_nonneg_left hmV (pow_nonneg hM 3))
  have hEr (i : Fin 3) : ‖er i‖ ≤ M*m :=
    map_bound (eH i (Tq x)) u M m (caps.reverse_high i) le_rfl hM
  have hIU : ‖IH u‖ ≤ M*m := map_bound IH u M m caps.high_inclusion le_rfl hM
  have hBU : ‖BU‖ ≤ M*m := map_bound (sphereSobolevShiftedDegreeL (3/2 : ℝ)) u M m caps.high_degree le_rfl hM
  have hOut (i : Fin 3) : ‖JL (er i)‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound JL (er i) M (M*m) caps.low_inclusion (hEr i) hM
      _ = M^2*m := by ring
  have hBout (i : Fin 3) : ‖(sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound (sphereSobolevShiftedDegreeL (1/2 : ℝ)) (er i) M (M*m)
        caps.low_degree (hEr i) hM
      _ = M^2*m := by ring
  have hRef (i j : Fin 3) : ‖eL j (Tq x) (D i)‖ ≤ M^2*V := by
    calc
      _ ≤ M*(M*V) := map_bound (eL j (Tq x)) (D i) M (M*V) (caps.reverse_low j) (caps.reference_input i) hM
      _ = M^2*V := by ring
  have hBh (j : Fin 3) : ‖eL j (Tq x) BU‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound (eL j (Tq x)) BU M (M*m) (caps.reverse_low j) hBU hM
      _ = M^2*m := by ring
  have hPlain (j : Fin 3) : ‖eL j (Tq x) (IH u)‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound (eL j (Tq x)) (IH u) M (M*m) (caps.reverse_low j) hIU hM
      _ = M^2*m := by ring
  have hGrad (i j : Fin 3) :
      ‖eL i (Tq x) (IH (fderiv ℝ Uin x (referenceMetricGramFrame g L (q,x) j)))‖ ≤ M^2*G := by
    calc
      _ ≤ M*(M*G) := map_bound (eL i (Tq x)) _ M (M*G) (caps.reverse_low i) (caps.frame_input j) hM
      _ = M^2*G := by ring
  have hDer (i j : Fin 3) :
      ‖(fderiv ℝ (fun z => eL i (Tq z)) x (referenceMetricGramFrame g L (q,x) j)) (IH u)‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound _ (IH u) M (M*m) (caps.reverse_low_directional i j) hIU hM
      _ = M^2*m := by ring
  have hConn (i j : Fin 3) : ‖referenceLowerHorizontalAngularL g L q x j (er i)‖ ≤ M^2*m := by
    calc
      _ ≤ M*(M*m) := map_bound _ (er i) M (M*m) (caps.low_connection j) (hEr i) hM
      _ = M^2*m := by ring
  have hFdeg (i j : Fin 3) :
      ‖f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)‖ ≤ M^3*V := by
    calc
      _ ≤ (M*beta)*(M^2*m) := smul_bound _ _ _ _ (caps.log_radius j) (hBout i) (mul_nonneg hM hb)
      _ = M^3*(beta*m) := by ring
      _ ≤ M^3*V := mul_le_mul_of_nonneg_left hbmV (pow_nonneg hM 3)
  have hWr (i j : Fin 3) : ‖Wr i j‖ ≤ 4*M^3*V := by
    have hh := norm_four_add
      (eL i (Tq x) (IH (fderiv ℝ Uin x (referenceMetricGramFrame g L (q,x) j))))
      ((fderiv ℝ (fun z => eL i (Tq z)) x (referenceMetricGramFrame g L (q,x) j)) (IH u))
      (referenceLowerHorizontalAngularL g L q x j (er i))
      (f j • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)) (M^3*V)
      ((hGrad i j).trans hG3) ((hDer i j).trans hm3) ((hConn i j).trans hm3) (hFdeg i j)
    exact hh.trans_eq (by ring)
  have hC (i j : Fin 3) : |c i j x| ≤ M*r^2 := by
    change |r^2*referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M*r^2
    rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact (mul_le_mul_of_nonneg_left (caps.principal i j) (sq_nonneg r)).trans_eq (mul_comm _ _)
  have hMC (i j : Fin 3) : |mu*c i j x| ≤ M^2*r^2 := by
    calc
      _ = |mu| *|c i j x| := abs_mul _ _
      _ ≤ M*(M*r^2) := mul_le_mul caps.density (hC i j) (abs_nonneg _) hM
      _ = M^2*r^2 := by ring
  have hMCF (i j k : Fin 3) : |mu*c i j x*f k| ≤ M^3*r^2*beta := by
    calc
      _ = |mu*c i j x| *|f k| := abs_mul _ _
      _ ≤ (M^2*r^2)*(M*beta) := mul_le_mul (hMC i j) (caps.log_radius k) (abs_nonneg _)
        (mul_nonneg (sq_nonneg M) (sq_nonneg r))
      _ = M^3*r^2*beta := by ring
  have hTwoMCF (i j k : Fin 3) : |2*(mu*c i j x*f k)| ≤ 2*M^3*r^2*beta := by
    calc
      _ = 2*|mu*c i j x*f k| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2*(M^3*r^2*beta) := mul_le_mul_of_nonneg_left (hMCF i j k) (by norm_num)
      _ = 2*M^3*r^2*beta := by ring
  have hMCG (i j k : Fin 3) : |mu*c i j x*Gamma i j k| ≤ M^3*r^2 := by
    calc
      _ = |mu*c i j x| *|Gamma i j k| := abs_mul _ _
      _ ≤ (M^2*r^2)*M := mul_le_mul (hMC i j) (caps.connection i j k) (abs_nonneg _)
        (mul_nonneg (sq_nonneg M) (sq_nonneg r))
      _ = M^3*r^2 := by ring
  have hDriftCoeff (i : Fin 3) : |mu*(r^2*normalizedSecondDriftFrameJoint g g2 L i (q,x))| ≤ M^2*r^2 := by
    calc
      _ = |mu| *(r^2*|normalizedSecondDriftFrameJoint g g2 L i (q,x)|) := by
        rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg r)]
      _ ≤ M*(r^2*M) := mul_le_mul caps.density
        (mul_le_mul_of_nonneg_left (caps.drift i) (sq_nonneg r))
        (mul_nonneg (sq_nonneg r) (abs_nonneg _)) hM
      _ = M^2*r^2 := by ring
  have hRefTerm (i j : Fin 3) : ‖(-(mu*c i j x)) • eL j (Tq x) (D i)‖ ≤ W0 := by
    calc
      _ ≤ (M^2*r^2)*(M^2*V) := smul_bound _ _ _ _ (by simpa only [abs_neg] using hMC i j)
        (hRef i j) (mul_nonneg (sq_nonneg M) (sq_nonneg r))
      _ = M^4*r^2*V := by ring
      _ ≤ M^5*r^2*V := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h45 (sq_nonneg r)) hV
  have hBhTerm (i j : Fin 3) : ‖(2*(mu*c i j x*f i)) • eL j (Tq x) BU‖ ≤ 2*W0 := by
    calc
      _ ≤ (2*M^3*r^2*beta)*(M^2*m) := smul_bound _ _ _ _ (hTwoMCF i j i) (hBh j) (by positivity)
      _ = (2*M^5*r^2)*(beta*m) := by ring
      _ ≤ (2*M^5*r^2)*V := mul_le_mul_of_nonneg_left hbmV (by positivity)
      _ = 2*W0 := by dsimp [W0]; ring
  have hPlainTerm (i j : Fin 3) :
      ‖densityDerivativeCoefficient g L q i (c i j) x • eL j (Tq x) (IH u)‖ ≤ W0 := by
    calc
      _ ≤ (M*r^2*beta)*(M^2*m) := smul_bound _ _ _ _ (caps.density_derivative i j i) (hPlain j) (by positivity)
      _ = (M^3*r^2)*(beta*m) := by ring
      _ ≤ (M^3*r^2)*V := mul_le_mul_of_nonneg_left hbmV (by positivity)
      _ ≤ (M^5*r^2)*V := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h35 (sq_nonneg r)) hV
      _ = W0 := rfl
  have hWrTerm (i j : Fin 3) : ‖(-(mu*c i j x)) • Wr i j‖ ≤ 4*W0 := by
    calc
      _ ≤ (M^2*r^2)*(4*M^3*V) := smul_bound _ _ _ _ (by simpa only [abs_neg] using hMC i j)
        (hWr i j) (mul_nonneg (sq_nonneg M) (sq_nonneg r))
      _ = 4*W0 := by dsimp [W0]; ring
  have hDegreeTerm (i j : Fin 3) :
      ‖(2*(mu*c i j x*f j)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg)‖ ≤ 2*W0 := by
    calc
      _ ≤ (2*M^3*r^2*beta)*(M^2*m) := smul_bound _ _ _ _ (hTwoMCF i j j) (hBout i) (by positivity)
      _ = (2*M^5*r^2)*(beta*m) := by ring
      _ ≤ (2*M^5*r^2)*V := mul_le_mul_of_nonneg_left hbmV (by positivity)
      _ = 2*W0 := by dsimp [W0]; ring
  have hOutDensityTerm (i j : Fin 3) :
      ‖densityDerivativeCoefficient g L q j (c i j) x • JL (er i)‖ ≤ W0 := by
    calc
      _ ≤ (M*r^2*beta)*(M^2*m) := smul_bound _ _ _ _ (caps.density_derivative i j j) (hOut i) (by positivity)
      _ = (M^3*r^2)*(beta*m) := by ring
      _ ≤ (M^3*r^2)*V := mul_le_mul_of_nonneg_left hbmV (by positivity)
      _ ≤ (M^5*r^2)*V := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h35 (sq_nonneg r)) hV
      _ = W0 := rfl
  have hExtra (i j : Fin 3) : ‖(mu*c i j x*f i) • JL (er j)‖ ≤ W0 := by
    calc
      _ ≤ (M^3*r^2*beta)*(M^2*m) := smul_bound _ _ _ _ (hMCF i j i) (hOut j) (by positivity)
      _ = (M^5*r^2)*(beta*m) := by ring
      _ ≤ (M^5*r^2)*V := mul_le_mul_of_nonneg_left hbmV (by positivity)
      _ = W0 := rfl
  have hConnectionTerm (i j k : Fin 3) : ‖(mu*c i j x*Gamma i j k) • JL (er k)‖ ≤ W0 := by
    calc
      _ ≤ (M^3*r^2)*(M^2*m) := smul_bound _ _ _ _ (hMCG i j k) (hOut k) (by positivity)
      _ = (M^5*r^2)*m := by ring
      _ ≤ (M^5*r^2)*V := mul_le_mul_of_nonneg_left hmV (by positivity)
      _ = W0 := rfl
  have hDriftTerm (i : Fin 3) :
      ‖(mu*(r^2*normalizedSecondDriftFrameJoint g g2 L i (q,x))) • JL (er i)‖ ≤ W0 := by
    calc
      _ ≤ (M^2*r^2)*(M^2*m) := smul_bound _ _ _ _ (hDriftCoeff i) (hOut i) (by positivity)
      _ = (M^4*r^2)*m := by ring
      _ ≤ (M^5*r^2)*m := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h45 (sq_nonneg r)) hm
      _ ≤ (M^5*r^2)*V := mul_le_mul_of_nonneg_left hmV (by positivity)
      _ = W0 := rfl
  let row1 := fun i j : Fin 3 =>
    (-(mu*c i j x)) • eL j (Tq x) (D i) +
      (2*(mu*c i j x*f i)) • eL j (Tq x) BU -
      densityDerivativeCoefficient g L q i (c i j) x • eL j (Tq x) (IH u)
  let row2 := fun i j : Fin 3 =>
    (-(mu*c i j x)) • Wr i j +
      (2*(mu*c i j x*f j)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg) -
      densityDerivativeCoefficient g L q j (c i j) x • JL (er i)
  let extra := fun i j : Fin 3 => (mu*c i j x*f i) • JL (er j)
  let conn := fun i j k : Fin 3 => (mu*c i j x*Gamma i j k) • JL (er k)
  let drift := fun i : Fin 3 => (mu*(r^2*normalizedSecondDriftFrameJoint g g2 L i (q,x))) • JL (er i)
  have hRow1 (i j : Fin 3) : ‖row1 i j‖ ≤ 4*W0 := by
    have hh := norm_add_sub
      ((-(mu*c i j x)) • eL j (Tq x) (D i))
      ((2*(mu*c i j x*f i)) • eL j (Tq x) BU)
      (densityDerivativeCoefficient g L q i (c i j) x • eL j (Tq x) (IH u))
    have h1 := hRefTerm i j
    have h2 := hBhTerm i j
    have h3 := hPlainTerm i j
    change ‖(-(mu*c i j x)) • eL j (Tq x) (D i) +
      (2*(mu*c i j x*f i)) • eL j (Tq x) BU -
      densityDerivativeCoefficient g L q i (c i j) x • eL j (Tq x) (IH u)‖ ≤ 4*W0
    linarith
  have hRow2 (i j : Fin 3) : ‖row2 i j‖ ≤ 7*W0 := by
    have hh := norm_add_sub
      ((-(mu*c i j x)) • Wr i j)
      ((2*(mu*c i j x*f j)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg))
      (densityDerivativeCoefficient g L q j (c i j) x • JL (er i))
    have h1 := hWrTerm i j
    have h2 := hDegreeTerm i j
    have h3 := hOutDensityTerm i j
    change ‖(-(mu*c i j x)) • Wr i j +
      (2*(mu*c i j x*f j)) • (sphereSobolevShiftedDegreeL (1/2 : ℝ) (er i) : Neg) -
      densityDerivativeCoefficient g L q j (c i j) x • JL (er i)‖ ≤ 7*W0
    linarith
  have hDensity : ‖SDN‖ ≤ 138*W0 :=
    density_rows_bound row1 row2 extra conn drift W0 hRow1 hRow2 hExtra hConnectionTerm hDriftTerm
  have hNorm : ‖SN‖ ≤ M*(138*W0) :=
    smul_bound _ _ M (138*W0) caps.density_inv hDensity hM
  have hFinal : M*(138*W0) ≤ 200*M^6*(r^2*G+r^2*beta*m) := by
    have hNonneg : 0 ≤ M^6*r^2*V := mul_nonneg
      (mul_nonneg (pow_nonneg hM 6) (sq_nonneg r)) hV
    calc
      M*(138*W0) = 138*(M^6*r^2*V) := by dsimp [W0]; ring
      _ ≤ 200*(M^6*r^2*V) := mul_le_mul_of_nonneg_right (by norm_num : (138 : ℝ) ≤ 200) hNonneg
      _ = 200*M^6*(r^2*G+r^2*beta*m) := by dsimp [V]; ring
  exact hNorm.trans hFinal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSAdjointSecondPointwiseBound
