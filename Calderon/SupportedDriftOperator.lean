import Calderon.StrongDerivativeValues
import Calderon.ClosedCoefficientMultiplier
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def strongLowerOrderCoordinateDerivativeL (hcalc : FixedSobolevCalculus) (s : ℕ) (i : Fin 3) :
    StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s).comp
    (strongCoordinateDerivativeL hcalc s i)

theorem strongLowerOrderCoordinateDerivative_value_ae (hcalc : FixedSobolevCalculus)
    (s : ℕ) (i : Fin 3) (u : StrongDirichletSpace s) :
    TauCeti.Wkp.value s (strongLowerOrderCoordinateDerivativeL hcalc s i u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) z) i := by
  change TauCeti.Wkp.value s (TauCeti.Wkp.lowerOrder s (strongCoordinateDerivativeL hcalc s i u)) =ᵐ[_] _
  rw [← TauCeti.Wkp.value_succ]
  exact strongCoordinateDerivative_value_ae hcalc s i u

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def weightedDriftCoordinate (w : P × R3 → ℝ) (b : P × R3 → R3) (i : Fin 3) (p : P × R3) : ℝ :=
  w p*b p i

theorem contDiff_weightedDriftCoordinate (w : P × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : P × R3 → R3) (hb : ContDiff ℝ ∞ b) (i : Fin 3) :
    ContDiff ℝ ∞ (weightedDriftCoordinate w b i) :=
  hw.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hb)

theorem weightedDriftCoordinate_support (w : P × R3 → ℝ) (b : P × R3 → R3)
    (K : Set R3) (hz : ∀ p z, z ∉ K → w (p,z)=0) (i : Fin 3) :
    ∀ p z, z ∉ K → weightedDriftCoordinate w b i (p,z)=0 := by
  intro p z h
  simp only [weightedDriftCoordinate,hz p z h,zero_mul]

def commonSupportWeightedDriftBaseOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : P × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : P × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (p : P) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  ∑ i : Fin 3, (coefficientMultiplier hcalc s
    (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
      (contDiff_weightedDriftCoordinate w hw b hb i) K hK
      (weightedDriftCoordinate_support w b K hz i) p)).comp
        (strongLowerOrderCoordinateDerivativeL hcalc s i)

theorem contDiff_commonSupportWeightedDriftBaseOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : P × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : P × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0) :
    ContDiff ℝ ∞ (commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz) := by
  apply ContDiff.sum
  intro i hi
  exact (contDiff_commonSupport_actual_coefficientMultiplier hcalc s
    (weightedDriftCoordinate w b i) (contDiff_weightedDriftCoordinate w hw b hb i)
    K hK (weightedDriftCoordinate_support w b K hz i)).clm_comp contDiff_const

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem commonSupportWeightedDriftBaseOperator_value_ae (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : P × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : P × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (p : P) (u : StrongDirichletSpace s) :
    TauCeti.Wkp.value s (commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => ∑ i : Fin 3, w (p,z)*b (p,z) i*
        (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) z) i := by
  let T (i : Fin 3) : BallSobolev s := coefficientMultiplier hcalc s
    (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
      (contDiff_weightedDriftCoordinate w hw b hb i) K hK
      (weightedDriftCoordinate_support w b K hz i) p)
        (strongLowerOrderCoordinateDerivativeL hcalc s i u)
  have hi (i : Fin 3) : TauCeti.Wkp.value s (T i) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => w (p,z)*b (p,z) i*
        (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) z) i := by
    have hmul := coefficientMultiplier_value_ae hcalc s
      (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
        (contDiff_weightedDriftCoordinate w hw b hb i) K hK
        (weightedDriftCoordinate_support w b K hz i) p)
      (strongLowerOrderCoordinateDerivativeL hcalc s i u)
    have hder := strongLowerOrderCoordinateDerivative_value_ae hcalc s i u
    apply (hmul.trans (Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ _) hder)).trans
    apply Filter.Eventually.of_forall
    intro z
    change coefficientValue (s+1)
      (commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
        (contDiff_weightedDriftCoordinate w hw b hb i) K hK
        (weightedDriftCoordinate_support w b K hz i) p) z * _ = _
    exact congrArg (fun t : ℝ => t *
      (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) z) i)
      (coefficientValue_commonSupportCoefficientFamily (s+1) (weightedDriftCoordinate w b i)
        (contDiff_weightedDriftCoordinate w hw b hb i) K hK
        (weightedDriftCoordinate_support w b K hz i) p z)
  change (TauCeti.Wkp.valueL s) (∑ i : Fin 3, T i) =ᵐ[_] _
  rw [map_sum]
  exact (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum (fun i _ => hi i))

end OAI.AnisotropicCalderon.DirichletFamily
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def commonSupportWeightedDriftOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
  (-L*p.2) • commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p

theorem contDiff_commonSupportWeightedDriftOperator (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0) (L : ℝ) :
    ContDiff ℝ ∞ (commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L) :=
  (contDiff_const.mul contDiff_snd).smul
    (contDiff_commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz)

theorem commonSupportWeightedDriftOperator_zero (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0) (L : ℝ) (y : R3) :
    commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L (y,0) = 0 := by
  simp [commonSupportWeightedDriftOperator]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem commonSupportWeightedDriftOperator_value_ae (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (p : R3 × ℝ) (u : StrongDirichletSpace s) :
    TauCeti.Wkp.value s (commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L p u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun z => (-L*p.2)*(∑ i : Fin 3, w (p,z)*b (p,z) i*
        (TauCeti.W1p.gradient (strongDirichletProjectionL s u : BallH1) z) i) := by
  change TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
    ((-L*p.2) • (commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p u)) =ᵐ[_] _
  rw [TauCeti.Wkp.value_smul]
  have hv := commonSupportWeightedDriftBaseOperator_value_ae hcalc s w hw b hb K hK hz p u
  exact (Lp.coeFn_smul (-L*p.2)
    (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p u))).trans
        (hv.const_smul (-L*p.2))

theorem exists_compact_commonSupportWeightedDriftOperator_bound (hcalc : FixedSobolevCalculus) (s : ℕ)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (q : Set (R3 × ℝ)) (hq : IsCompact q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q,
      ‖commonSupportWeightedDriftOperator hcalc s w hw b hb K hK hz L p‖ ≤ |L| * C * |p.2| := by
  obtain ⟨C,hC⟩ := hq.exists_bound_of_continuousOn
    (contDiff_commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz).continuous.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p hp
  calc
    _ = |L| * |p.2| * ‖commonSupportWeightedDriftBaseOperator hcalc s w hw b hb K hK hz p‖ := by
      simp only [commonSupportWeightedDriftOperator,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg]
    _ ≤ |L| * |p.2| * max C 0 := mul_le_mul_of_nonneg_left
      ((hC p hp).trans (le_max_left _ _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring
end OAI.AnisotropicCalderon.DirichletFamily
