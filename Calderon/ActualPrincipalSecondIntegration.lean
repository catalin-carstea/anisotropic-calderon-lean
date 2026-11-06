import Calderon.LocalizedPrincipalSecondForm
import Calderon.AmbientAngularShift

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualPrincipalSecondIntegration
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  BaseDensityAdjoint ReferenceDensityBounds PrincipalCommutator NaturalAngularAdjoint
  AngularShiftGraph HarmonicDerivativeOperator BalancedAngularShift BalancedFrameAngularShift
  ActualPrincipalErrorCoefficient ActualPrincipalErrorForm ActualScalarPrincipalAdjoint
  ActualPerturbedDefect PerturbedDensityAdjoint ConformalDepth LocalizedPrincipalSecondForm
  SectionFiveErrorForms

lemma contDiff_principalSecondFrameCoefficient (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (i j l : Fin 3) :
    ContDiff ℝ ∞ (principalSecondFrameCoefficient a c i j l) := by
  unfold principalSecondFrameCoefficient
  apply ContDiff.sum
  intro k hk
  exact (((hc l k).mul (contDiff_directionalFDeriv (coordinateDirection k) _ (ha i j))).neg.add
    ((ha k i).mul (contDiff_directionalFDeriv (coordinateDirection k) _ (hc l j)))).add
    ((ha k j).mul (contDiff_directionalFDeriv (coordinateDirection k) _ (hc l i)))

lemma contDiff_actualPrincipalSecondFrameCoefficient (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun x => h x i j))
    (i j l : Fin 3) : ContDiff ℝ ∞ (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l) :=
  contDiff_principalSecondFrameCoefficient _ _
    (contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh)
    (fun l k => (contDiff_referenceFrameEntryFamily g hg L l k).comp
      (contDiff_const.prodMk contDiff_id)) i j l

lemma contDiff_actualPrincipalSecondBalancedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun x => h x i j))
    (i j : Fin 3) :
    ContDiff ℝ ∞ (actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j) := by
  unfold actualPrincipalSecondBalancedRaising balancedRaisingCombination
  apply ContDiff.sum
  intro l hl
  exact (contDiff_actualPrincipalSecondFrameCoefficient g hg L lam δ R p h hδ hR hh i j l).smul
    contDiff_const

/-- The derivative of the actual unscaled sandwich is the sandwich of Dp, with no beta term. -/
lemma directional_actualPrincipalSecondBalancedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun x => h x i j))
    (i j m : Fin 3) (x : R3) :
    fderiv ℝ (actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j) x
        (coordinateDirection m) =
      balancedRaisingCombination hF hO hD (fun l => directionalFDeriv (coordinateDirection m)
        (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l) x) := by
  change directionalFDeriv (coordinateDirection m)
    (fun y => ∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l y •
      balancedRaising hF hO hD l) x = _
  have hsmooth (l : Fin 3) : ContDiff ℝ ∞ (fun y =>
      actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l y •
        balancedRaising hF hO hD l) :=
    (contDiff_actualPrincipalSecondFrameCoefficient g hg L lam δ R p h hδ hR hh i j l).smul
      contDiff_const
  unfold directionalFDeriv balancedRaisingCombination
  rw [fderiv_fun_sum (fun l _ => (hsmooth l).differentiable (by simp) x)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro l hl
  have ht := PrincipalCommutator.directionalFDeriv_smul (coordinateDirection m)
    (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l)
    (fun _ => balancedRaising hF hO hD l)
    (contDiff_actualPrincipalSecondFrameCoefficient g hg L lam δ R p h hδ hR hh i j l)
    contDiff_const x
  simpa only [PrincipalCommutator.directionalFDeriv, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, smul_zero, add_zero] using ht

/-- The adjoint output is explicitly constructed from genuine raising fields. -/
def actualPrincipalSecondAdjointField (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (raising : Fin 3 → R3 → SphereL2) (i j : Fin 3) : R3 → SphereL2 :=
  fun x => ∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x • raising l x

lemma contDiff_actualPrincipalSecondAdjointField (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (hδ : 0 < δ) (hR : 0 < R) (hh : ∀ i j, ContDiff ℝ ∞ (fun x => h x i j))
    (raising : Fin 3 → R3 → SphereL2) (hr : ∀ l, ContDiff ℝ ∞ (raising l)) (i j : Fin 3) :
    ContDiff ℝ ∞ (actualPrincipalSecondAdjointField g L lam δ R p h raising i j) := by
  unfold actualPrincipalSecondAdjointField
  apply ContDiff.sum
  intro l hl
  exact (contDiff_actualPrincipalSecondFrameCoefficient g hg L lam δ R p h hδ hR hh i j l).smul (hr l)

lemma actualPrincipalSecondAdjointField_inverse_half_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (phi phiHalf : R3 → SphereL2) (raising : Fin 3 → R3 → SphereL2)
    (hhalf : ∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2))
    (hr : ∀ l x, (phi x,raising l x) ∈ sphereRaisingGraph hF hO hD l)
    (i j : Fin 3) (x : R3) :
    (actualPrincipalSecondAdjointField g L lam δ R p h raising i j x,
      actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j x (phiHalf x)) ∈
        sphereBesselGraph hO hD (-(1/2)) := by
  rw [actualPrincipalSecondBalancedRaising,balancedRaisingCombination_of_graph hF hO hD _
    (phi x) (phiHalf x) (fun l => raising l x) (hhalf x) (fun l => hr l x)]
  exact halfDegreeMultiplier_graph hO hD _

lemma directionalDeriv_fixed_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (X : R3) (u : R3 → E) (hu : ContDiff ℝ ∞ u) (x : R3) :
    fderiv ℝ (fun y => T (u y)) x X = T (fderiv ℝ u x X) := by
  have hd := T.hasFDerivAt.comp x (hu.differentiable (by simp) x).hasFDerivAt
  change (fderiv ℝ (T ∘ u) x) X = _
  rw [hd.fderiv]
  rfl

/-- Differentiation in a fixed base direction preserves the actual unbounded angular graph. -/
lemma directionalDeriv_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (X : R3) (u d : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hd : ContDiff ℝ ∞ d)
    (hgraph : ∀ x, (u x,d x) ∈ sphereDerivativeGraph hF hO hD l) (x : R3) :
    (directionalDeriv X u x,directionalDeriv X d x) ∈ sphereDerivativeGraph hF hO hD l := by
  intro k
  have he : (fun y => sphereHarmonicCoordinate hO hD k (d y)) =
      fun y => harmonicDerivative hF k l (sphereHarmonicCoordinate hO hD (k+1) (u y)) :=
    funext (fun y => hgraph y k)
  have hdiff := congrArg (fun f => fderiv ℝ f x X) he
  rw [directionalDeriv_fixed_clm _ X d hd x,
    directionalDeriv_fixed_clm (harmonicDerivative hF k l) X
      (fun y => sphereHarmonicCoordinate hO hD (k+1) (u y))
      ((sphereHarmonicCoordinate hO hD (k+1)).contDiff.comp hu) x,
    directionalDeriv_fixed_clm _ X u hu x] at hdiff
  exact hdiff

lemma second_directionalDeriv_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (X Y : R3) (u d : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hd : ContDiff ℝ ∞ d)
    (hgraph : ∀ x, (u x,d x) ∈ sphereDerivativeGraph hF hO hD l) (x : R3) :
    (directionalDeriv X (directionalDeriv Y u) x,
      directionalDeriv X (directionalDeriv Y d) x) ∈ sphereDerivativeGraph hF hO hD l :=
  directionalDeriv_sphereDerivativeGraph hF hO hD l X _ _
    (contDiff_directionalDeriv Y u hu) (contDiff_directionalDeriv Y d hd)
    (directionalDeriv_sphereDerivativeGraph hF hO hD l Y u d hu hd hgraph) x

/-- Exact transpose of the actual p angular term, with every ordered tensor slot retained. -/
lemma actual_principal_second_transpose (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (phi : R3 → SphereL2) (derivative raising : Fin 3 → R3 → SphereL2)
    (hphi : ContDiff ℝ ∞ phi) (hd : ∀ l, ContDiff ℝ ∞ (derivative l))
    (hdgraph : ∀ l x, (phi x,derivative l x) ∈ sphereDerivativeGraph hF hO hD l)
    (hrgraph : ∀ l x, (phi x,raising l x) ∈ sphereRaisingGraph hF hO hD l)
    (i j : Fin 3) (x : R3) :
    ⟪∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x •
        directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
          (derivative l)) x,phi x⟫_ℝ =
      ⟪directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j) phi) x,
        actualPrincipalSecondAdjointField g L lam δ R p h raising i j x⟫_ℝ := by
  simp only [actualPrincipalSecondAdjointField,inner_sum, sum_inner,
    real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro l hl
  rw [sphereDerivativeGraph_inner_adjoint hF hO hD l _ _ _ _
    (second_directionalDeriv_sphereDerivativeGraph hF hO hD l
      (coordinateDirection i) (coordinateDirection j) phi (derivative l) hphi (hd l) (hdgraph l) x)
    (hrgraph l x)]

/-- The raw, unnormalized actual principal contribution, before the source factor two. -/
def actualPrincipalSecondForm (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (phi : R3 → SphereL2) (derivative : Fin 3 → R3 → SphereL2) (i j : Fin 3) : ℝ :=
  ∫ x, referenceDensityFamily g L (lam,x) *
    ⟪∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x •
      directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j)
        (derivative l)) x,phi x⟫_ℝ

/-- Bounds for unscaled Kp and DKp follow from the already derived actual scalar jets. -/
theorem exists_actual_principal_second_raising_uniform_bounds (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ P Pd : ℝ, 0 < P ∧ 0 < Pd ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps → ∀ i j m,
        ‖actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j x‖ ≤ P*eps/beta ∧
        ‖fderiv ℝ (actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j) x
          (coordinateDirection m)‖ ≤ Pd*eps := by
  obtain ⟨P,Pd,hP,hPd,hcoeff⟩ := exists_actual_principal_second_frame_uniform_bounds g hg L hL K hK
  refine ⟨6*P,6*Pd,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i j m
  have hc (l : Fin 3) := hcoeff lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet
    hb hsmall i j l m
  constructor
  · have ht := norm_raisingCombination_le_of_bound hF hO hD _ (P*eps/beta) (fun l => (hc l).1)
    convert ht using 1 <;> first | rfl | ring
  · rw [directional_actualPrincipalSecondBalancedRaising hF hO hD g hg L lam δ R p h hδ hR hh i j m x]
    have ht := norm_raisingCombination_le_of_bound hF hO hD _ (Pd*eps) (fun l => (hc l).2)
    convert ht using 1 <;> first | rfl | ring

/-- Actual p contribution on a smooth angular graph core. The adjoint field is constructed;
the sole integrability input is discharged for actual ambient compact fields below. -/
theorem exists_actual_principal_second_core_form_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p →
      let beta : R3 → ℝ := fun x => metricDifferentialNorm
        (referenceMetric (dilatedMetric g lam) L) (fun y => Real.log (referenceRadius δ R p L y)) x
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ beta x) → (∀ x ∈ K, referenceRadius δ R p L x * (beta x)^2 ≤ eps) →
      ∀ phi phiHalf phiOne phiThree : R3 → SphereL2,
      ∀ derivative raising : Fin 3 → R3 → SphereL2,
      ContDiff ℝ ∞ phi → ContDiff ℝ ∞ phiHalf →
      (∀ l, ContDiff ℝ ∞ (derivative l)) → (∀ l, ContDiff ℝ ∞ (raising l)) →
      HasCompactSupport phi → tsupport phi ⊆ K →
      (∀ x, (phi x,phiHalf x) ∈ sphereBesselGraph hO hD (1/2)) →
      (∀ x, (phi x,phiOne x) ∈ sphereBesselGraph hO hD 1) →
      (∀ x, (phi x,phiThree x) ∈ sphereBesselGraph hO hD (3/2)) →
      (∀ l x, (phi x,derivative l x) ∈ sphereDerivativeGraph hF hO hD l) →
      (∀ l x, (phi x,raising l x) ∈ sphereRaisingGraph hF hO hD l) →
      Integrable (fun x => referenceDensityFamily g L (lam,x) * sourceNormSquareIntegrand
        (beta x) (fun k : Fin 3 => directionalDeriv (coordinateDirection k) phi x)
        (phiOne x) (fun k : Fin 3 => directionalDeriv (coordinateDirection k) phiHalf x) (phiThree x)) →
      ∀ i j, |actualPrincipalSecondForm g L lam δ R p h phi derivative i j| ≤
        C*eps * sourceNormSquare g L lam beta
          (fun (x : R3) (k : Fin 3) => directionalDeriv (coordinateDirection k) phi x) phiOne
          (fun (x : R3) (k : Fin 3) => directionalDeriv (coordinateDirection k) phiHalf x) phiThree := by
  obtain ⟨P,Pd,hP,hPd,hraising⟩ :=
    exists_actual_principal_second_raising_uniform_bounds hF hO hD g hg L hL K hK
  obtain ⟨Cmu,hCmu,hdmu⟩ := exists_reference_density_relative_first_bound g hg L K hK
  refine ⟨P+Cmu*P+Pd,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp beta eps heps heps1 h hh hhjet hb hsmall
    phi phiHalf phiOne phiThree derivative raising hphi hphiHalf hd hr hcompact hsupport
    hhalf hone hthree hdgraph hrgraph hN i j
  let q := actualPrincipalSecondAdjointField g L lam δ R p h raising i j
  let Kp := actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j
  have hKp : ContDiff ℝ ∞ Kp :=
    contDiff_actualPrincipalSecondBalancedRaising hF hO hD g hg L lam δ R p h hδ hR hh i j
  have hq : ContDiff ℝ ∞ q :=
    contDiff_actualPrincipalSecondAdjointField g hg L lam δ R p h hδ hR hh raising hr i j
  have hKbound (x : R3) (hx : x ∈ K) : ‖Kp x‖ ≤ P*eps/beta x :=
    (hraising lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
      (hb x hx) (hsmall x hx) i j i).1
  have hDKbound (x : R3) (hx : x ∈ K) : ‖fderiv ℝ Kp x (coordinateDirection i)‖ ≤ Pd*eps :=
    (hraising lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh (hhjet x hx)
      (hb x hx) (hsmall x hx) i j i).2
  have hqgraph (x : R3) : (q x,Kp x (phiHalf x)) ∈ sphereBesselGraph hO hD (-(1/2)) :=
    actualPrincipalSecondAdjointField_inverse_half_graph hF hO hD g L lam δ R p h
      phi phiHalf raising hhalf hrgraph i j x
  have hform : actualPrincipalSecondForm g L lam δ R p h phi derivative i j =
      ∫ x, referenceDensityFamily g L (lam,x) *
        ⟪directionalDeriv (coordinateDirection i) (directionalDeriv (coordinateDirection j) phi) x,q x⟫_ℝ := by
    unfold actualPrincipalSecondForm
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => congrArg
      (fun t => referenceDensityFamily g L (lam,x)*t)
      (actual_principal_second_transpose hF hO hD g L lam δ R p h phi derivative raising
        hphi hd hdgraph hrgraph i j x))
  rw [hform]
  exact compact_unscaled_second_error_form_bound hO hD g hg L lam eps heps
    coordinateDirection i j beta K hb phi phiHalf phiOne phiThree q hphi hphiHalf hq
    hcompact hsupport hhalf hone hthree Kp hKp hqgraph Cmu P Pd hCmu.le hP.le hPd.le
    hKbound hDKbound (fun x hx => hdmu lam hlam x hx i) hN

/-- All nine ordered base slots and the exact source factor two. -/
lemma factor_two_nine_sum_bound (F : Fin 3 → Fin 3 → ℝ) (B : ℝ)
    (hF : ∀ i j, |F i j| ≤ B) : |2 * ∑ i, ∑ j, F i j| ≤ 18*B := by
  have hs (i : Fin 3) : |∑ j, F i j| ≤ 3*B := by
    calc
      _ ≤ ∑ j, |F i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 3, B := Finset.sum_le_sum (fun j _ => hF i j)
      _ = _ := by simp
  calc
    _ = 2*|∑ i, ∑ j, F i j| := by rw [abs_mul]; norm_num
    _ ≤ 2*(∑ i, |∑ j, F i j|) := mul_le_mul_of_nonneg_left
      (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2*(∑ _i : Fin 3, 3*B) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => hs i)) (by norm_num)
    _ = _ := by simp; ring

end OAI.AnisotropicCalderon.ActualPrincipalSecondIntegration
