import Calderon.ActualPrincipalAdjointHigherJets
import Calderon.NaturalAngularAdjointIntegration
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualScalarPrincipalSelfCommutator
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
  ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect
  ActualPrincipalErrorCoefficient ActualPrincipalAdjointDerivative
  ActualPrincipalAdjointHigherJets NaturalAngularAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scalarFirstZeroBase (v : Fin 3 → R3) (b : Fin 3 → R3 → ℝ)
    (c : R3 → ℝ) (u : R3 → E) (x : R3) : E :=
  c x • u x + ∑ l, b l x • directionalFDeriv (v l) u x

def scalarPrincipalAdjointDefect (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) : R3 → E :=
  scalarFirstZeroBase v (fun l y => adjointFirstCoefficient v mu a y l)
    (adjointZeroCoefficient v mu a) u

/-- Genuine commutator of the existing density adjoint and the existing scalar second-base part. -/
def scalarPrincipalSelfCommutator (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) (x : R3) : E :=
  scalarSecondBaseAdjoint v mu a (scalarSecondBase v a u) x -
    scalarSecondBase v a (scalarSecondBaseAdjoint v mu a u) x

lemma contDiff_adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0)
    (i : Fin 3) : ContDiff ℝ ∞ (fun y => adjointFirstCoefficient v mu a y i) := by
  exact (contDiff_const.mul (hm.inv hp)).mul (ContDiff.sum
    (fun j _ => contDiff_directionalFDeriv (v j) _ (hm.mul (ha i j))))

lemma contDiff_adjointZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hp : ∀ x, mu x ≠ 0) :
    ContDiff ℝ ∞ (adjointZeroCoefficient v mu a) := by
  exact (hm.inv hp).mul (ContDiff.sum (fun i _ => ContDiff.sum
    (fun j _ => contDiff_directionalFDeriv (v j) _
      (contDiff_directionalFDeriv (v i) _ (hm.mul (ha i j))))))

lemma contDiff_scalarFirstZeroBase (v : Fin 3 → R3) (b : Fin 3 → R3 → ℝ)
    (c : R3 → ℝ) (u : R3 → E) (hb : ∀ l, ContDiff ℝ ∞ (b l))
    (hc : ContDiff ℝ ∞ c) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (scalarFirstZeroBase v b c u) := by
  exact (hc.smul hu).add (ContDiff.sum
    (fun l _ => (hb l).smul (contDiff_directionalFDeriv (v l) u hu)))

lemma hasCompactSupport_scalarFirstZeroBase (v : Fin 3 → R3)
    (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E)
    (hc : HasCompactSupport u) : HasCompactSupport (scalarFirstZeroBase v b c u) := by
  have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun l _ =>
    (hc.fderiv_apply (𝕜 := ℝ) (v l)).smul_left (f := b l))
  have ht := (hc.smul_left (f := c)).add hs
  convert ht using 1
  funext x
  simp only [scalarFirstZeroBase,directionalFDeriv,Finset.sum_apply,Pi.add_apply,Pi.smul_apply']

lemma directional_second_add_hilbert (i j : R3) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    directionalFDeriv i (directionalFDeriv j (fun y => u y+w y)) x =
      directionalFDeriv i (directionalFDeriv j u) x +
      directionalFDeriv i (directionalFDeriv j w) x := by
  have he : directionalFDeriv j (fun y => u y+w y) =
      fun y => directionalFDeriv j u y+directionalFDeriv j w y :=
    funext (directionalFDeriv_add j u w hu hw)
  rw [he,directionalFDeriv_add i _ _
    (contDiff_directionalFDeriv j u hu) (contDiff_directionalFDeriv j w hw)]

lemma scalarSecondBase_add (v : Fin 3 → R3) (a : MatrixField) (u w : R3 → E)
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (x : R3) :
    scalarSecondBase v a (fun y => u y+w y) x =
      scalarSecondBase v a u x+scalarSecondBase v a w x := by
  simp only [scalarSecondBase,directional_second_add_hilbert _ _ u w hu hw,
    smul_add,Finset.sum_add_distrib]

/-- The scalar defect is the actual bD+c from the existing adjoint coefficients. -/
lemma scalarSecondBaseAdjoint_eq_add_defect (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u)
    (hp : ∀ x, mu x ≠ 0) (hs : ∀ x, (a x).IsHermitian) (x : R3) :
    scalarSecondBaseAdjoint v mu a u x = scalarSecondBase v a u x+
      scalarPrincipalAdjointDefect v mu a u x := by
  have h := scalarSecondBaseAdjoint_coefficient_form v mu a u hm ha hu x (hp x)
    (Filter.Eventually.of_forall hs)
  change scalarSecondBaseAdjoint v mu a u x-scalarSecondBase v a u x =
    scalarPrincipalAdjointDefect v mu a u x at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- The genuine self-commutator equals the commutator of the computed first/zero defect. -/
lemma scalarPrincipalSelfCommutator_eq_defect_commutator (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u)
    (hp : ∀ x, mu x ≠ 0) (hs : ∀ x, (a x).IsHermitian) (x : R3) :
    scalarPrincipalSelfCommutator v mu a u x =
      scalarPrincipalAdjointDefect v mu a (scalarSecondBase v a u) x -
        scalarSecondBase v a (scalarPrincipalAdjointDefect v mu a u) x := by
  have hd : ContDiff ℝ ∞ (scalarPrincipalAdjointDefect v mu a u) :=
    contDiff_scalarFirstZeroBase v _ _ u
      (contDiff_adjointFirstCoefficient v mu a hm ha hp)
      (contDiff_adjointZeroCoefficient v mu a hm ha hp) hu
  have he : scalarSecondBaseAdjoint v mu a u =
      fun y => scalarSecondBase v a u y+scalarPrincipalAdjointDefect v mu a u y :=
    funext (scalarSecondBaseAdjoint_eq_add_defect v mu a u hm ha hu hp hs)
  unfold scalarPrincipalSelfCommutator
  rw [scalarSecondBaseAdjoint_eq_add_defect v mu a _ hm ha
    (contDiff_scalarSecondBase v a u ha hu) hp hs x,he,
    scalarSecondBase_add v a _ _ (contDiff_scalarSecondBase v a u ha hu) hd x]
  module

/-- Each scalar first/second term cancels its literal third section derivatives. -/
lemma scalar_first_second_commutator (i j l : R3) (a b : R3 → ℝ) (u : R3 → E)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hu : ContDiff ℝ ∞ u) (x : R3) :
    b x • directionalFDeriv l (fun y => a y •
      directionalFDeriv i (directionalFDeriv j u) y) x -
      a x • directionalFDeriv i (directionalFDeriv j
        (fun y => b y • directionalFDeriv l u y)) x =
      (b x*directionalFDeriv l a x) • directionalFDeriv i (directionalFDeriv j u) x -
      (a x*directionalFDeriv i (directionalFDeriv j b) x) • directionalFDeriv l u x -
      (a x*directionalFDeriv j b x) • directionalFDeriv i (directionalFDeriv l u) x -
      (a x*directionalFDeriv i b x) • directionalFDeriv j (directionalFDeriv l u) x := by
  rw [directionalFDeriv_smul l a _ ha
    (contDiff_directionalFDeriv i _ (contDiff_directionalFDeriv j u hu)),
    directionalFDeriv_second_smul j i b _ hb (contDiff_directionalFDeriv l u hu),
    directionalFDeriv_third_commute i j l u hu]
  simp only [smul_add,smul_smul]
  module

lemma scalar_zero_second_commutator (i j : R3) (a c : R3 → ℝ) (u : R3 → E)
    (hc : ContDiff ℝ ∞ c) (hu : ContDiff ℝ ∞ u) (x : R3) :
    c x • (a x • directionalFDeriv i (directionalFDeriv j u) x) -
      a x • directionalFDeriv i (directionalFDeriv j (fun y => c y • u y)) x =
      -(a x*directionalFDeriv i (directionalFDeriv j c) x) • u x -
      (a x*directionalFDeriv j c x) • directionalFDeriv i u x -
      (a x*directionalFDeriv i c x) • directionalFDeriv j u x := by
  rw [directionalFDeriv_second_smul j i c u hc hu]
  simp only [smul_add,smul_smul,neg_smul]
  module

lemma hasCompactSupport_scalarSecondBaseAdjoint (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (u : R3 → E) (hc : HasCompactSupport u) :
    HasCompactSupport (scalarSecondBaseAdjoint v mu a u) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
    HasCompactSupport.finset_sum (s := Finset.univ) (fun j _ =>
      (((hc.smul_left (f := fun y => mu y*a y i j)).fderiv_apply (𝕜 := ℝ) (v i)).fderiv_apply
        (𝕜 := ℝ) (v j))))
  have ht := h.smul_left (f := fun y => (mu y)⁻¹)
  convert ht using 1
  funext x
  rfl

/-- The genuine weighted commutator form is the actual difference of the two operator squares. -/
theorem compact_scalarPrincipalSelfCommutator_square_difference (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hp : ∀ x, 0 < mu x) :
    (∫ x, mu x * ⟪scalarPrincipalSelfCommutator v mu a u x,u x⟫_ℝ) =
      (∫ x, mu x * ‖scalarSecondBase v a u x‖^2) -
        (∫ x, mu x * ‖scalarSecondBaseAdjoint v mu a u x‖^2) := by
  have hp0 : ∀ x, mu x ≠ 0 := fun x => ne_of_gt (hp x)
  have hs := contDiff_scalarSecondBase v a u ha hu
  have hsA := contDiff_scalarSecondBaseAdjoint v mu a u hm ha hu hp0
  have hcA := hasCompactSupport_scalarSecondBaseAdjoint v mu a u hc
  have hL := compact_scalarSecondBase_adjoint v mu a u (scalarSecondBase v a u)
    hm ha hu hs hc hp
  have hR := compact_scalarSecondBase_adjoint v mu a (scalarSecondBaseAdjoint v mu a u) u
    hm ha hsA hu hcA hp
  have hiL := compact_weighted_inner_integrable mu
    (scalarSecondBaseAdjoint v mu a (scalarSecondBase v a u)) u hm.continuous
    (contDiff_scalarSecondBaseAdjoint v mu a _ hm ha hs hp0).continuous hu.continuous
    (hasCompactSupport_scalarSecondBaseAdjoint v mu a _ (hasCompactSupport_scalarSecondBase v a u hc))
  have hiR := compact_weighted_inner_integrable mu
    (scalarSecondBase v a (scalarSecondBaseAdjoint v mu a u)) u hm.continuous
    (contDiff_scalarSecondBase v a _ ha hsA).continuous hu.continuous
    (hasCompactSupport_scalarSecondBase v a _ hcA)
  simp only [scalarPrincipalSelfCommutator,inner_sub_left,mul_sub]
  rw [integral_sub hiL hiR]
  have hL' : (∫ x, mu x * ⟪scalarSecondBaseAdjoint v mu a (scalarSecondBase v a u) x,u x⟫_ℝ) =
      ∫ x, mu x * ‖scalarSecondBase v a u x‖^2 := by
    simpa only [real_inner_comm,real_inner_self_eq_norm_sq] using hL.symm
  have hR' : (∫ x, mu x * ⟪scalarSecondBase v a (scalarSecondBaseAdjoint v mu a u) x,u x⟫_ℝ) =
      ∫ x, mu x * ‖scalarSecondBaseAdjoint v mu a u x‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using hR
  rw [hL',hR']

lemma compact_weighted_norm_sq_integrable (mu : R3 → ℝ) (u : R3 → E)
    (hm : Continuous mu) (hu : Continuous u) (hc : HasCompactSupport u) :
    Integrable (fun x => mu x*‖u x‖^2) := by
  simpa only [real_inner_self_eq_norm_sq] using
    compact_weighted_inner_integrable mu u u hm hu hu hc

/-- The true commutator form only uses one U2 factor paired with its computed defect. -/
theorem compact_scalarPrincipalSelfCommutator_defect_form (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hp : ∀ x, 0 < mu x) (hs : ∀ x, (a x).IsHermitian) :
    (∫ x, mu x * ⟪scalarPrincipalSelfCommutator v mu a u x,u x⟫_ℝ) =
      -2*(∫ x, mu x * ⟪scalarSecondBase v a u x,scalarPrincipalAdjointDefect v mu a u x⟫_ℝ) -
        (∫ x, mu x * ‖scalarPrincipalAdjointDefect v mu a u x‖^2) := by
  have hp0 : ∀ x, mu x ≠ 0 := fun x => ne_of_gt (hp x)
  let S := scalarSecondBase v a u
  let SA := scalarSecondBaseAdjoint v mu a u
  let d := scalarPrincipalAdjointDefect v mu a u
  have hS : ContDiff ℝ ∞ S := contDiff_scalarSecondBase v a u ha hu
  have hSA : ContDiff ℝ ∞ SA := contDiff_scalarSecondBaseAdjoint v mu a u hm ha hu hp0
  have hd : ContDiff ℝ ∞ d := contDiff_scalarFirstZeroBase v _ _ u
    (contDiff_adjointFirstCoefficient v mu a hm ha hp0)
    (contDiff_adjointZeroCoefficient v mu a hm ha hp0) hu
  have hcS := hasCompactSupport_scalarSecondBase v a u hc
  have hcSA := hasCompactSupport_scalarSecondBaseAdjoint v mu a u hc
  have hcd : HasCompactSupport d := hasCompactSupport_scalarFirstZeroBase v _ _ u hc
  have hiS := compact_weighted_norm_sq_integrable mu S hm.continuous hS.continuous hcS
  have hiSA := compact_weighted_norm_sq_integrable mu SA hm.continuous hSA.continuous hcSA
  have hid := compact_weighted_norm_sq_integrable mu d hm.continuous hd.continuous hcd
  have hip := compact_weighted_inner_integrable mu S d hm.continuous hS.continuous hd.continuous hcS
  have he (x : R3) : SA x = S x+d x :=
    scalarSecondBaseAdjoint_eq_add_defect v mu a u hm ha hu hp0 hs x
  have hpw (x : R3) : mu x*‖S x‖^2-mu x*‖SA x‖^2 =
      -2*(mu x*⟪S x,d x⟫_ℝ)-mu x*‖d x‖^2 := by
    rw [he x,norm_add_sq_real]
    ring
  rw [compact_scalarPrincipalSelfCommutator_square_difference v mu a u hm ha hu hc hp]
  change (∫ x, mu x*‖S x‖^2)-(∫ x, mu x*‖SA x‖^2) = _
  rw [← integral_sub hiS hiSA]
  simp_rw [hpw]
  rw [integral_sub (hip.const_mul (-2)) hid,integral_const_mul]

/-- One actual compact base integration by parts, expanded into scalar coefficient derivatives. -/
lemma compact_first_one_parts (i : R3) (A : R3 → ℝ) (u w : R3 → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) :
    (∫ x, A x*⟪directionalFDeriv i u x,w x⟫_ℝ) =
      -(∫ x, directionalFDeriv i A x*⟪u x,w x⟫_ℝ) -
        (∫ x, A x*⟪u x,directionalFDeriv i w x⟫_ℝ) := by
  have ht := BaseDensityAdjoint.compact_weighted_first_adjoint i (fun _ : R3 => (1 : ℝ)) A
    u w contDiff_const hA hu hw hc
  have ht' : (∫ x, A x*⟪directionalFDeriv i u x,w x⟫_ℝ) =
      -(∫ x, ⟪directionalFDeriv i (fun y => A y•w y) x,u x⟫_ℝ) := by
    simpa only [one_mul,BaseDensityAdjoint.directionalDeriv,directionalFDeriv] using ht
  have ha := compact_weighted_inner_integrable (directionalFDeriv i A) u w
    (contDiff_directionalFDeriv i A hA).continuous hu.continuous hw.continuous hc
  have hb := compact_weighted_inner_integrable A u (directionalFDeriv i w)
    hA.continuous hu.continuous (contDiff_directionalFDeriv i w hw).continuous hc
  rw [ht']
  simp_rw [directionalFDeriv_smul i A w hA hw,inner_add_left,real_inner_smul_left,real_inner_comm]
  rw [integral_add ha hb]
  ring

lemma compact_second_one_parts (i j : R3) (A : R3 → ℝ) (u w : R3 → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) :
    (∫ x, A x*⟪directionalFDeriv i (directionalFDeriv j u) x,w x⟫_ℝ) =
      -(∫ x, directionalFDeriv i A x*⟪directionalFDeriv j u x,w x⟫_ℝ) -
        (∫ x, A x*⟪directionalFDeriv j u x,directionalFDeriv i w x⟫_ℝ) :=
  compact_first_one_parts i A _ w hA (contDiff_directionalFDeriv j u hu) hw
    (hc.fderiv_apply (𝕜 := ℝ) j)

/-- An individual cubic section term is a first-jet form; repeated directions are permitted. -/
theorem compact_cubic_term_first_jet_form (i j l : R3) (A : R3 → ℝ) (u : R3 → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    2*(∫ x, A x*⟪directionalFDeriv i (directionalFDeriv j u) x,directionalFDeriv l u x⟫_ℝ) =
      -(∫ x, directionalFDeriv i A x*⟪directionalFDeriv j u x,directionalFDeriv l u x⟫_ℝ) -
      (∫ x, directionalFDeriv j A x*⟪directionalFDeriv i u x,directionalFDeriv l u x⟫_ℝ) +
      (∫ x, directionalFDeriv l A x*⟪directionalFDeriv i u x,directionalFDeriv j u x⟫_ℝ) := by
  have hi := contDiff_directionalFDeriv i u hu
  have hj := contDiff_directionalFDeriv j u hu
  have hl := contDiff_directionalFDeriv l u hu
  have hp1 := compact_second_one_parts i j A u (directionalFDeriv l u) hA hu hl hc
  have hp2 := compact_second_one_parts j i A u (directionalFDeriv l u) hA hu hl hc
  have he : directionalFDeriv j (directionalFDeriv i u) =
      directionalFDeriv i (directionalFDeriv j u) :=
    funext (directionalFDeriv_commute j i u hu)
  rw [he] at hp2
  have hp3 := compact_first_one_parts l A (directionalFDeriv i u) (directionalFDeriv j u)
    hA hi hj (hc.fderiv_apply (𝕜 := ℝ) i)
  have hli : directionalFDeriv l (directionalFDeriv i u) =
      directionalFDeriv i (directionalFDeriv l u) :=
    funext (directionalFDeriv_commute l i u hu)
  have hlj : directionalFDeriv l (directionalFDeriv j u) =
      directionalFDeriv j (directionalFDeriv l u) :=
    funext (directionalFDeriv_commute l j u hu)
  rw [hli,hlj] at hp3
  have hp3' : (∫ x, A x*⟪directionalFDeriv j u x,
      directionalFDeriv i (directionalFDeriv l u) x⟫_ℝ) =
      -(∫ x, directionalFDeriv l A x*⟪directionalFDeriv i u x,directionalFDeriv j u x⟫_ℝ) -
        (∫ x, A x*⟪directionalFDeriv i u x,
          directionalFDeriv j (directionalFDeriv l u) x⟫_ℝ) := by
    convert hp3 using 1
    congr 1
    funext x
    rw [real_inner_comm]
  linarith

def scalarSecondFirstCrossForm (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (b : Fin 3 → R3 → ℝ) (u : R3 → E) : ℝ :=
  ∑ i, ∑ j, ∑ l, ∫ x, mu x*a x i j*b l x *
    ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,directionalFDeriv (v l) u x⟫_ℝ

def scalarSecondZeroCrossForm (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (c : R3 → ℝ) (u : R3 → E) : ℝ :=
  ∑ i, ∑ j, ∫ x, mu x*a x i j*c x *
    ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,u x⟫_ℝ

/-- All integrals in the reduced form contain at most first derivatives of the section. -/
def scalarReducedSelfForm (v : Fin 3 → R3) (mu : R3 → ℝ) (a : MatrixField)
    (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E) : ℝ :=
  (∑ i, ∑ j, ∑ l,
    ((∫ x, directionalFDeriv (v i) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (v j) u x,directionalFDeriv (v l) u x⟫_ℝ) +
    (∫ x, directionalFDeriv (v j) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (v i) u x,directionalFDeriv (v l) u x⟫_ℝ) -
    (∫ x, directionalFDeriv (v l) (fun y => mu y*a y i j*b l y) x *
      ⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ))) +
  (∑ i, ∑ j,
    (2*(∫ x, directionalFDeriv (v i) (fun y => mu y*a y i j*c y) x *
      ⟪directionalFDeriv (v j) u x,u x⟫_ℝ) +
    2*(∫ x, mu x*a x i j*c x *
      ⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ))) -
  (∫ x, mu x*‖scalarFirstZeroBase v b c u x‖^2)

lemma compact_scalar_second_defect_cross_form (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hb : ∀ l, ContDiff ℝ ∞ (b l)) (hc : ContDiff ℝ ∞ c)
    (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) :
    (∫ x, mu x*⟪scalarSecondBase v a u x,scalarFirstZeroBase v b c u x⟫_ℝ) =
      scalarSecondZeroCrossForm v mu a c u+scalarSecondFirstCrossForm v mu a b u := by
  have hD (i j : Fin 3) : ContDiff ℝ ∞ (directionalFDeriv (v i) (directionalFDeriv (v j) u)) :=
    contDiff_directionalFDeriv (v i) _ (contDiff_directionalFDeriv (v j) u hu)
  have hcompD (i j : Fin 3) : HasCompactSupport (directionalFDeriv (v i) (directionalFDeriv (v j) u)) :=
    (hcompact.fderiv_apply (𝕜 := ℝ) (v j)).fderiv_apply (𝕜 := ℝ) (v i)
  have hz (i j : Fin 3) : Integrable (fun x => mu x*a x i j*c x *
      ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,u x⟫_ℝ) :=
    compact_weighted_inner_integrable (fun x => mu x*a x i j*c x) _ u
      (((hm.mul (ha i j)).mul hc).continuous) (hD i j).continuous hu.continuous (hcompD i j)
  have hf (i j l : Fin 3) : Integrable (fun x => mu x*a x i j*b l x *
      ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,directionalFDeriv (v l) u x⟫_ℝ) :=
    compact_weighted_inner_integrable (fun x => mu x*a x i j*b l x) _ _
      (((hm.mul (ha i j)).mul (hb l)).continuous) (hD i j).continuous
      (contDiff_directionalFDeriv (v l) u hu).continuous (hcompD i j)
  have he (x : R3) : mu x*⟪scalarSecondBase v a u x,scalarFirstZeroBase v b c u x⟫_ℝ =
      ∑ i, ∑ j, (mu x*a x i j*c x *
        ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,u x⟫_ℝ +
        ∑ l, mu x*a x i j*b l x *
          ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,directionalFDeriv (v l) u x⟫_ℝ) := by
    simp only [scalarSecondBase,scalarFirstZeroBase,sum_inner,inner_sum,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,Finset.mul_sum,mul_add,Fin.sum_univ_three]
    ring
  let Z : Fin 3 → Fin 3 → R3 → ℝ := fun i j x => mu x*a x i j*c x *
    ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,u x⟫_ℝ
  let F : Fin 3 → Fin 3 → Fin 3 → R3 → ℝ := fun i j l x => mu x*a x i j*b l x *
    ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,directionalFDeriv (v l) u x⟫_ℝ
  have hZi : (∫ x, ∑ i, ∑ j, Z i j x) = ∑ i, ∑ j, ∫ x, Z i j x := by
    rw [integral_finsetSum (f := fun i x => ∑ j, Z i j x) Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hz i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hz i j)
  have hFi : (∫ x, ∑ i, ∑ j, ∑ l, F i j l x) = ∑ i, ∑ j, ∑ l, ∫ x, F i j l x := by
    rw [integral_finsetSum (f := fun i x => ∑ j, ∑ l, F i j l x) Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun l _ => hf i j l)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum (f := fun j x => ∑ l, F i j l x) Finset.univ
      (fun j _ => integrable_finsetSum Finset.univ (fun l _ => hf i j l))]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finsetSum Finset.univ (fun l _ => hf i j l)
  have hsumZ : Integrable (fun x => ∑ i, ∑ j, Z i j x) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hz i j))
  have hsumF : Integrable (fun x => ∑ i, ∑ j, ∑ l, F i j l x) :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun l _ => hf i j l)))
  calc
    _ = ∫ x, (∑ i, ∑ j, Z i j x) + (∑ i, ∑ j, ∑ l, F i j l x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [Z,F,Finset.sum_add_distrib] using he x)
    _ = (∫ x, ∑ i, ∑ j, Z i j x) + (∫ x, ∑ i, ∑ j, ∑ l, F i j l x) :=
      integral_add hsumZ hsumF
    _ = _ := by rw [hZi,hFi]; rfl

/-- Two integrations remove the cubic section terms without a fourth coefficient derivative. -/
theorem compact_scalar_defect_cross_reduced_form (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (b : Fin 3 → R3 → ℝ) (c : R3 → ℝ) (u : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hb : ∀ l, ContDiff ℝ ∞ (b l)) (hc : ContDiff ℝ ∞ c)
    (hu : ContDiff ℝ ∞ u) (hcompact : HasCompactSupport u) :
    -2*(∫ x, mu x*⟪scalarSecondBase v a u x,scalarFirstZeroBase v b c u x⟫_ℝ) -
      (∫ x, mu x*‖scalarFirstZeroBase v b c u x‖^2) = scalarReducedSelfForm v mu a b c u := by
  have hz (i j : Fin 3) := compact_second_one_parts (v i) (v j)
    (fun x => mu x*a x i j*c x) u u ((hm.mul (ha i j)).mul hc) hu hu hcompact
  have hf (i j l : Fin 3) := compact_cubic_term_first_jet_form (v i) (v j) (v l)
    (fun x => mu x*a x i j*b l x) u ((hm.mul (ha i j)).mul (hb l)) hu hcompact
  have hz' (i j : Fin 3) : -2*(∫ x, mu x*a x i j*c x *
      ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,u x⟫_ℝ) =
      2*(∫ x, directionalFDeriv (v i) (fun y => mu y*a y i j*c y) x *
        ⟪directionalFDeriv (v j) u x,u x⟫_ℝ) +
      2*(∫ x, mu x*a x i j*c x *
        ⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ) := by
    have ht := hz i j
    have heinner (x : R3) :
        ⟪directionalFDeriv (v j) u x,directionalFDeriv (v i) u x⟫_ℝ =
        ⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ := real_inner_comm _ _
    simp_rw [heinner] at ht
    linarith
  have hf' (i j l : Fin 3) : -2*(∫ x, mu x*a x i j*b l x *
      ⟪directionalFDeriv (v i) (directionalFDeriv (v j) u) x,directionalFDeriv (v l) u x⟫_ℝ) =
      (∫ x, directionalFDeriv (v i) (fun y => mu y*a y i j*b l y) x *
        ⟪directionalFDeriv (v j) u x,directionalFDeriv (v l) u x⟫_ℝ) +
      (∫ x, directionalFDeriv (v j) (fun y => mu y*a y i j*b l y) x *
        ⟪directionalFDeriv (v i) u x,directionalFDeriv (v l) u x⟫_ℝ) -
      (∫ x, directionalFDeriv (v l) (fun y => mu y*a y i j*b l y) x *
        ⟪directionalFDeriv (v i) u x,directionalFDeriv (v j) u x⟫_ℝ) := by linarith [hf i j l]
  rw [compact_scalar_second_defect_cross_form v mu a b c u hm ha hb hc hu hcompact]
  unfold scalarSecondZeroCrossForm scalarSecondFirstCrossForm scalarReducedSelfForm
  rw [mul_add]
  simp only [Finset.mul_sum,hz',hf']
  ring

/-- The actual scalar-principal self-commutator is exactly the first-jet reduced form. -/
theorem compact_scalarPrincipalSelfCommutator_reduced_form (v : Fin 3 → R3)
    (mu : R3 → ℝ) (a : MatrixField) (u : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hp : ∀ x, 0 < mu x) (hs : ∀ x, (a x).IsHermitian) :
    (∫ x, mu x*⟪scalarPrincipalSelfCommutator v mu a u x,u x⟫_ℝ) =
      scalarReducedSelfForm v mu a (fun l y => adjointFirstCoefficient v mu a y l)
        (adjointZeroCoefficient v mu a) u := by
  rw [compact_scalarPrincipalSelfCommutator_defect_form v mu a u hm ha hu hc hp hs]
  exact compact_scalar_defect_cross_reduced_form v mu a _ _ u hm ha
    (contDiff_adjointFirstCoefficient v mu a hm ha (fun x => ne_of_gt (hp x)))
    (contDiff_adjointZeroCoefficient v mu a hm ha (fun x => ne_of_gt (hp x))) hu hc

end OAI.AnisotropicCalderon.ActualScalarPrincipalSelfCommutator
