import Calderon.BoundedAngularShift
import Calderon.AmbientAngularShift

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.BalancedAngularShift
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SpectralWeightedGraph AngularShiftGraph BoundedSpectralMultiplier
  BoundedAngularShift HarmonicDerivativeOperator SmoothAngularApplication
  AmbientAngularShift

/-- The exact source half-order inverse weight, including the constant mode. -/
def halfDegreeWeight (k : ℕ) : ℝ := besselWeight (-(1/2 : ℝ)) k

lemma halfDegreeWeight_pos (k : ℕ) : 0 < halfDegreeWeight k :=
  besselWeight_pos _ k

lemma abs_halfDegreeWeight_le_one (k : ℕ) : |halfDegreeWeight k| ≤ 1 := by
  rw [abs_of_pos (halfDegreeWeight_pos k)]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))])
    (by norm_num)

lemma halfDegreeWeight_succ_le (k : ℕ) :
    halfDegreeWeight (k+1) ≤ halfDegreeWeight k := by
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (by norm_num) (by norm_num)

lemma halfDegreeWeight_mul_self (k : ℕ) :
    halfDegreeWeight k * halfDegreeWeight k = inverseDegreeWeight k := by
  unfold halfDegreeWeight besselWeight inverseDegreeWeight
  rw [← Real.rpow_add (by positivity)]
  norm_num [Real.rpow_neg_one]

lemma degree_mul_halfDegreeWeight_sq (k : ℕ) :
    (1+(k:ℝ)) * (halfDegreeWeight k * halfDegreeWeight k) = 1 := by
  rw [halfDegreeWeight_mul_self]
  simp [inverseDegreeWeight,show (1+(k:ℝ)) ≠ 0 by positivity]

lemma halfDegreeWeight_mul_positive_half (k : ℕ) :
    halfDegreeWeight k * besselWeight (1/2 : ℝ) k = 1 := by
  unfold halfDegreeWeight besselWeight
  rw [← Real.rpow_add (by positivity)]
  norm_num

/-- An actual bounded W_{-1/2}, never an application of a raw unbounded shift. -/
def halfDegreeMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD halfDegreeWeight 1 (by norm_num)
    abs_halfDegreeWeight_le_one

lemma halfDegreeMultiplier_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (halfDegreeMultiplier hO hD u) =
      halfDegreeWeight k • sphereHarmonicCoordinate hO hD k u :=
  boundedSpectralMultiplier_mem hO hD halfDegreeWeight 1 (by norm_num)
    abs_halfDegreeWeight_le_one u k

lemma halfDegreeMultiplier_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) :
    (u,halfDegreeMultiplier hO hD u) ∈ sphereBesselGraph hO hD (-(1/2 : ℝ)) :=
  halfDegreeMultiplier_coordinate hO hD u

lemma halfDegreeMultiplier_of_positive_half_graph (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u U : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    halfDegreeMultiplier hO hD U = u := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (halfDegreeMultiplier hO hD U) =
    sphereHarmonicCoordinate hO hD k u
  rw [halfDegreeMultiplier_coordinate,hU k,smul_smul,
    halfDegreeWeight_mul_positive_half,one_smul]

lemma norm_halfDegreeMultiplier_le (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : ‖halfDegreeMultiplier hO hD‖ ≤ 1 :=
  norm_boundedSpectralMultiplier_le hO hD halfDegreeWeight 1 (by norm_num)
    abs_halfDegreeWeight_le_one

/-- q_D(0)=0; q_D(k+1)=(k+2)w_k w_{k+1}. -/
def derivativeBalanceWeight : ℕ → ℝ
  | 0 => 0
  | k+1 => (1+((k+1):ℝ)) * halfDegreeWeight k * halfDegreeWeight (k+1)

/-- q_R keeps the constant input and raises it to degree one. -/
def raisingBalanceWeight (k : ℕ) : ℝ :=
  (1+(k:ℝ)) * halfDegreeWeight k * halfDegreeWeight (k+1)

lemma abs_derivativeBalanceWeight_le_two (k : ℕ) :
    |derivativeBalanceWeight k| ≤ 2 := by
  cases k with
  | zero => norm_num [derivativeBalanceWeight]
  | succ k =>
    have hw := halfDegreeWeight_succ_le k
    have hn := (halfDegreeWeight_pos k).le
    have hn' := (halfDegreeWeight_pos (k+1)).le
    have hd : (1:ℝ)+((k+1):ℝ) ≤ 2*(1+(k:ℝ)) := by
      norm_num
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k:ℝ))]
    rw [derivativeBalanceWeight,abs_of_nonneg (by positivity)]
    calc
      (1+((k+1):ℝ)) * halfDegreeWeight k * halfDegreeWeight (k+1)
          ≤ (1+((k+1):ℝ)) * (halfDegreeWeight k * halfDegreeWeight k) := by
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left hw (mul_nonneg (by positivity) hn)
      _ ≤ (2*(1+(k:ℝ))) * (halfDegreeWeight k * halfDegreeWeight k) :=
        mul_le_mul_of_nonneg_right hd (mul_nonneg hn hn)
      _ = 2 := by rw [mul_assoc,degree_mul_halfDegreeWeight_sq,mul_one]

lemma abs_raisingBalanceWeight_le_one (k : ℕ) :
    |raisingBalanceWeight k| ≤ 1 := by
  have hw := halfDegreeWeight_succ_le k
  have hn := (halfDegreeWeight_pos k).le
  have hn' := (halfDegreeWeight_pos (k+1)).le
  rw [raisingBalanceWeight,abs_of_nonneg (by positivity)]
  calc
    (1+(k:ℝ)) * halfDegreeWeight k * halfDegreeWeight (k+1)
        ≤ (1+(k:ℝ)) * (halfDegreeWeight k * halfDegreeWeight k) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hw
            (mul_nonneg (by positivity) (halfDegreeWeight_pos k).le)
    _ = 1 := degree_mul_halfDegreeWeight_sq k

lemma inverse_mul_derivativeBalanceWeight (k : ℕ) :
    inverseDegreeWeight (k+1) * derivativeBalanceWeight (k+1) =
      halfDegreeWeight k * halfDegreeWeight (k+1) := by
  unfold inverseDegreeWeight derivativeBalanceWeight
  have hd : (1+((k+1):ℝ)) ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one] at *
  field_simp [hd]

lemma inverse_mul_raisingBalanceWeight (k : ℕ) :
    inverseDegreeWeight k * raisingBalanceWeight k =
      halfDegreeWeight k * halfDegreeWeight (k+1) := by
  unfold inverseDegreeWeight raisingBalanceWeight
  have hd : (1+(k:ℝ)) ≠ 0 := by positivity
  field_simp [hd]

/-- Bounded scalar normalization preceding the already checked A_i W_{-1}. -/
def derivativeBalanceMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD derivativeBalanceWeight 2 (by norm_num)
    abs_derivativeBalanceWeight_le_two

def raisingBalanceMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) : SphereL2 →L[ℝ] SphereL2 :=
  boundedSpectralMultiplier hO hD raisingBalanceWeight 1 (by norm_num)
    abs_raisingBalanceWeight_le_one

lemma derivativeBalanceMultiplier_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (derivativeBalanceMultiplier hO hD u) =
      derivativeBalanceWeight k • sphereHarmonicCoordinate hO hD k u :=
  boundedSpectralMultiplier_mem hO hD derivativeBalanceWeight 2 (by norm_num)
    abs_derivativeBalanceWeight_le_two u k

lemma raisingBalanceMultiplier_coordinate (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (u : SphereL2) (k : ℕ) :
    sphereHarmonicCoordinate hO hD k (raisingBalanceMultiplier hO hD u) =
      raisingBalanceWeight k • sphereHarmonicCoordinate hO hD k u :=
  boundedSpectralMultiplier_mem hO hD raisingBalanceWeight 1 (by norm_num)
    abs_raisingBalanceWeight_le_one u k

/-- The genuine bounded extension of W_{-1/2} A_i W_{-1/2}. -/
def balancedDerivative (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  (normalizedDerivative hF hO hD i).comp (derivativeBalanceMultiplier hO hD)

/-- The genuine bounded extension of W_{-1/2} A_i* W_{-1/2}. -/
def balancedRaising (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (i : Fin 3) : SphereL2 →L[ℝ] SphereL2 :=
  (normalizedRaising hF hO hD i).comp (raisingBalanceMultiplier hO hD)

lemma norm_balancedDerivative_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    ‖balancedDerivative hF hO hD i‖ ≤ 4 := by
  calc
    ‖balancedDerivative hF hO hD i‖ ≤
        ‖normalizedDerivative hF hO hD i‖ * ‖derivativeBalanceMultiplier hO hD‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * 2 := mul_le_mul (norm_normalizedDerivative_le hF hO hD i)
      (norm_boundedSpectralMultiplier_le hO hD derivativeBalanceWeight 2 (by norm_num)
        abs_derivativeBalanceWeight_le_two) (norm_nonneg _) (by norm_num)
    _ = 4 := by norm_num

lemma norm_balancedRaising_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3) :
    ‖balancedRaising hF hO hD i‖ ≤ 2 := by
  calc
    ‖balancedRaising hF hO hD i‖ ≤
        ‖normalizedRaising hF hO hD i‖ * ‖raisingBalanceMultiplier hO hD‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2 * 1 := mul_le_mul (norm_normalizedRaising_le hF hO hD i)
      (norm_boundedSpectralMultiplier_le hO hD raisingBalanceWeight 1 (by norm_num)
        abs_raisingBalanceWeight_le_one) (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

/-- m=0 includes the genuine degree-one to degree-zero lowering output. -/
lemma balancedDerivative_coordinate (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) (m : ℕ) :
    sphereHarmonicCoordinate hO hD m (balancedDerivative hF hO hD i u) =
      (halfDegreeWeight m * halfDegreeWeight (m+1)) •
        harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u) := by
  change sphereHarmonicCoordinate hO hD m
      (normalizedDerivativeOutput hF hO hD i (derivativeBalanceMultiplier hO hD u)) = _
  rw [normalizedDerivativeOutput_graph hF hO hD i _ m,
    inverseDegreeMultiplier_coordinate,derivativeBalanceMultiplier_coordinate]
  simp only [map_smul,smul_smul]
  rw [inverse_mul_derivativeBalanceWeight]

lemma balancedRaising_coordinate_zero (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) : sphereHarmonicCoordinate hO hD 0
      (balancedRaising hF hO hD i u) = 0 :=
  (normalizedRaisingOutput_graph hF hO hD i (raisingBalanceMultiplier hO hD u)).1

/-- m=0 retains the nontrivial raising action on constant input. -/
lemma balancedRaising_coordinate_succ (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u : SphereL2) (m : ℕ) :
    sphereHarmonicCoordinate hO hD (m+1) (balancedRaising hF hO hD i u) =
      (halfDegreeWeight m * halfDegreeWeight (m+1)) •
        harmonicDerivativeAdjoint hF m i (sphereHarmonicCoordinate hO hD m u) := by
  change sphereHarmonicCoordinate hO hD (m+1)
      (normalizedRaisingOutput hF hO hD i (raisingBalanceMultiplier hO hD u)) = _
  rw [(normalizedRaisingOutput_graph hF hO hD i _).2 m,
    inverseDegreeMultiplier_coordinate,raisingBalanceMultiplier_coordinate]
  simp only [map_smul,smul_smul]
  rw [inverse_mul_raisingBalanceWeight]

lemma balancedDerivative_graph_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2)
    (hv : (halfDegreeMultiplier hO hD u,v) ∈ sphereDerivativeGraph hF hO hD i) :
    balancedDerivative hF hO hD i u = halfDegreeMultiplier hO hD v := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  change sphereHarmonicCoordinate hO hD m (balancedDerivative hF hO hD i u) =
    sphereHarmonicCoordinate hO hD m (halfDegreeMultiplier hO hD v)
  rw [balancedDerivative_coordinate,halfDegreeMultiplier_coordinate,hv m,
    halfDegreeMultiplier_coordinate,map_smul,smul_smul]

lemma balancedRaising_graph_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u v : SphereL2)
    (hv : (halfDegreeMultiplier hO hD u,v) ∈ sphereRaisingGraph hF hO hD i) :
    balancedRaising hF hO hD i u = halfDegreeMultiplier hO hD v := by
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext m
  change sphereHarmonicCoordinate hO hD m (balancedRaising hF hO hD i u) =
    sphereHarmonicCoordinate hO hD m (halfDegreeMultiplier hO hD v)
  cases m with
  | zero => rw [balancedRaising_coordinate_zero,halfDegreeMultiplier_coordinate,hv.1,smul_zero]
  | succ m =>
    rw [balancedRaising_coordinate_succ,halfDegreeMultiplier_coordinate,hv.2 m,
      halfDegreeMultiplier_coordinate,map_smul,smul_smul,mul_comm]

/-- On genuine core outputs, the balanced map realizes the source two-sided sandwich. -/
lemma balancedDerivative_of_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U v : SphereL2) (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : (u,v) ∈ sphereDerivativeGraph hF hO hD i) :
    balancedDerivative hF hO hD i U = halfDegreeMultiplier hO hD v := by
  apply balancedDerivative_graph_realization hF hO hD i U v
  rw [halfDegreeMultiplier_of_positive_half_graph hO hD u U hU]
  exact hv

lemma balancedRaising_of_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U v : SphereL2) (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hv : (u,v) ∈ sphereRaisingGraph hF hO hD i) :
    balancedRaising hF hO hD i U = halfDegreeMultiplier hO hD v := by
  apply balancedRaising_graph_realization hF hO hD i U v
  rw [halfDegreeMultiplier_of_positive_half_graph hO hD u U hU]
  exact hv

lemma balancedDerivative_ambient_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    balancedDerivative hF hO hD i
        (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG x) =
      halfDegreeMultiplier hO hD (ambientDerivativeField hF hO hD i G hG x) :=
  balancedDerivative_of_graph hF hO hD i _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG x)
    (ambientDerivativeField_graph hF hO hD i G hG x)

lemma balancedRaising_ambient_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    balancedRaising hF hO hD i
        (ambientBesselField hO hD (1/2 : ℝ) (by norm_num) G hG x) =
      halfDegreeMultiplier hO hD (ambientRaisingField hF hO hD i G hG x) :=
  balancedRaising_of_graph hF hO hD i _ _ _
    (ambientBesselField_graph hO hD (1/2 : ℝ) (by norm_num) G hG x)
    (ambientRaisingField_graph hF hO hD i G hG x)


/-- Half-weight self-adjunction against a genuine positive-half graph pair. -/
lemma inner_eq_halfDegreeMultiplier (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (du v V : SphereL2)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪du,v⟫_ℝ = ⟪halfDegreeMultiplier hO hD du,V⟫_ℝ := by
  have h := spectralGraph_inner_symm hO hD halfDegreeWeight
    du (halfDegreeMultiplier hO hD du) V (halfDegreeMultiplier hO hD V)
    (halfDegreeMultiplier_graph hO hD du) (halfDegreeMultiplier_graph hO hD V)
  rw [halfDegreeMultiplier_of_positive_half_graph hO hD v V hV] at h
  exact h.symm

lemma balancedDerivative_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U du v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : (u,du) ∈ sphereDerivativeGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪du,v⟫_ℝ = ⟪balancedDerivative hF hO hD i U,V⟫_ℝ := by
  rw [balancedDerivative_of_graph hF hO hD i u U du hU hdu]
  exact inner_eq_halfDegreeMultiplier hO hD du v V hV

/-- Genuine half-order form estimate; neither input is required to have zero mean. -/
lemma abs_inner_derivative_le_half_norm (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U du v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : (u,du) ∈ sphereDerivativeGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪du,v⟫_ℝ| ≤ 4 * ‖U‖ * ‖V‖ := by
  rw [balancedDerivative_inner_realization hF hO hD i u U du v V hU hdu hV]
  have hb : ‖balancedDerivative hF hO hD i U‖ ≤ 4 * ‖U‖ :=
    ((balancedDerivative hF hO hD i).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (norm_balancedDerivative_le hF hO hD i) (norm_nonneg U))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg V))

lemma balancedRaising_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U ru v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : (u,ru) ∈ sphereRaisingGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪ru,v⟫_ℝ = ⟪balancedRaising hF hO hD i U,V⟫_ℝ := by
  rw [balancedRaising_of_graph hF hO hD i u U ru hU hru]
  exact inner_eq_halfDegreeMultiplier hO hD ru v V hV

lemma abs_inner_raising_le_half_norm (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (i : Fin 3)
    (u U ru v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : (u,ru) ∈ sphereRaisingGraph hF hO hD i)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪ru,v⟫_ℝ| ≤ 2 * ‖U‖ * ‖V‖ := by
  rw [balancedRaising_inner_realization hF hO hD i u U ru v V hU hru hV]
  have hb : ‖balancedRaising hF hO hD i U‖ ≤ 2 * ‖U‖ :=
    ((balancedRaising hF hO hD i).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (norm_balancedRaising_le hF hO hD i) (norm_nonneg U))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg V))

end OAI.AnisotropicCalderon.BalancedAngularShift
