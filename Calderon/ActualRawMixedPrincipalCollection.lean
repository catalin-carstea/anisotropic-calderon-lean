import Calderon.ActualScalarPrincipalSelfCommutator
import Calderon.ActualPrincipalSecondIntegration
import Calderon.AmbientPrincipalSecondIntegration

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualRawMixedPrincipalCollection
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds ActualScalarPrincipalAdjoint
  ActualPerturbedDefect ActualPrincipalErrorCoefficient ActualScalarPrincipalSelfCommutator
  ActualPrincipalSecondIntegration NaturalAngularAdjoint ActualPrincipalErrorForm
  SmoothAngularApplication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Literal coordinate first-base part of T0 dagger, on constructed angular derivative outputs. -/
def frameLoweringFirst (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (x : R3) : E :=
  ∑ l, ∑ k, (-c l k x) • directionalFDeriv (coordinateDirection k) (d l) x

/-- The raw first-base/principal commutator, before source factors or estimates. -/
def frameLoweringFirstPrincipalCommutator (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E) (x : R3) : E :=
  frameLoweringFirst c (fun l => scalarSecondBase coordinateDirection a (d l)) x-
    scalarSecondBase coordinateDirection a (frameLoweringFirst c d) x

def framePrincipalSecondPart (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (x : R3) : E :=
  ∑ i, ∑ j, ∑ l, principalSecondFrameCoefficient a c i j l x •
    directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x

/-- Literal remaining first-base term. It is not supplied with a desired form bound. -/
def framePrincipalFirstRemainder (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (x : R3) : E :=
  ∑ l, ∑ k, ∑ i, ∑ j,
    (a x i j*directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) (c l k)) x) •
        directionalFDeriv (coordinateDirection k) (d l) x

lemma sum_four_reorder_ijlk (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → E) :
    (∑ l, ∑ k, ∑ i, ∑ j, F l k i j) = ∑ i, ∑ j, ∑ l, ∑ k, F l k i j := by
  calc
    _ = ∑ l, ∑ i, ∑ k, ∑ j, F l k i j := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ k, ∑ j, F l k i j := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, F l k i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma sum_four_reorder_iklj (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → E) :
    (∑ l, ∑ k, ∑ i, ∑ j, F l k i j) = ∑ i, ∑ k, ∑ l, ∑ j, F l k i j := by
  calc
    _ = ∑ l, ∑ i, ∑ k, ∑ j, F l k i j := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ k, ∑ j, F l k i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma sum_four_reorder_kjli (F : Fin 3 → Fin 3 → Fin 3 → Fin 3 → E) :
    (∑ l, ∑ k, ∑ i, ∑ j, F l k i j) = ∑ k, ∑ j, ∑ l, ∑ i, F l k i j := by
  calc
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F l k i j := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, F l k i j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

lemma scalarSecondBase_fintype_sum {ι : Type*} [Fintype ι]
    (v : Fin 3 → R3) (a : MatrixField) (F : ι → R3 → E)
    (hF : ∀ z, ContDiff ℝ ∞ (F z)) (x : R3) :
    scalarSecondBase v a (fun y => ∑ z, F z y) x = ∑ z, scalarSecondBase v a (F z) x := by
  classical
  unfold scalarSecondBase
  simp_rw [directionalFDeriv_second_fintype_sum _ _ F hF x,Finset.smul_sum]
  calc
    _ = ∑ i, ∑ z, ∑ j, a x i j • directionalFDeriv (v i) (directionalFDeriv (v j) (F z)) x := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Negative frame scalar first terms cancel literal third section derivatives. -/
lemma lowering_directional_principal_commutator (i j k : R3) (a c : R3 → ℝ)
    (u : R3 → E) (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c)
    (hu : ContDiff ℝ ∞ u) (x : R3) :
    (-c x) • directionalFDeriv k (fun y => a y • directionalFDeriv i (directionalFDeriv j u) y) x-
      a x • directionalFDeriv i (directionalFDeriv j
        (fun y => (-c y) • directionalFDeriv k u y)) x =
      (-(c x*directionalFDeriv k a x)) • directionalFDeriv i (directionalFDeriv j u) x+
      (a x*directionalFDeriv i (directionalFDeriv j c) x) • directionalFDeriv k u x+
      (a x*directionalFDeriv j c x) • directionalFDeriv i (directionalFDeriv k u) x+
      (a x*directionalFDeriv i c x) • directionalFDeriv j (directionalFDeriv k u) x := by
  have he : directionalFDeriv j (fun y => -c y) = fun y => -directionalFDeriv j c y :=
    funext (directional_neg j c hc)
  have hsecond : directionalFDeriv i (directionalFDeriv j (fun y => -c y)) x =
      -directionalFDeriv i (directionalFDeriv j c) x := by
    rw [he,directional_neg i _ (contDiff_directionalFDeriv j c hc)]
  have h := scalar_first_second_commutator i j k a (fun y => -c y) u ha hc.neg hu x
  rw [hsecond,directional_neg i c hc,directional_neg j c hc] at h
  calc
    _ = _ := h
    _ = _ := by
      simp only [neg_mul,mul_neg,neg_smul]
      abel

lemma frameLoweringFirstPrincipalCommutator_expansion (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hd : ∀ l, ContDiff ℝ ∞ (d l)) (x : R3) :
    frameLoweringFirstPrincipalCommutator a c d x = ∑ l, ∑ k, ∑ i, ∑ j, (
      (-(c l k x*directionalFDeriv (coordinateDirection k) (fun y => a y i j) x)) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x+
      (a x i j*directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection j) (c l k)) x) •
          directionalFDeriv (coordinateDirection k) (d l) x+
      (a x i j*directionalFDeriv (coordinateDirection j) (c l k) x) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) (d l)) x+
      (a x i j*directionalFDeriv (coordinateDirection i) (c l k) x) •
        directionalFDeriv (coordinateDirection j) (directionalFDeriv (coordinateDirection k) (d l)) x) := by
  let F : Fin 3 → Fin 3 → R3 → E := fun l k y =>
    (-c l k y) • directionalFDeriv (coordinateDirection k) (d l) y
  have hF (l k : Fin 3) : ContDiff ℝ ∞ (F l k) :=
    (hc l k).neg.smul (contDiff_directionalFDeriv _ _ (hd l))
  have hs (l : Fin 3) : ContDiff ℝ ∞ (fun y => ∑ k, F l k y) :=
    ContDiff.sum (fun k _ => hF l k)
  have hright : scalarSecondBase coordinateDirection a (frameLoweringFirst c d) x =
      ∑ l, ∑ k, scalarSecondBase coordinateDirection a (F l k) x := by
    change scalarSecondBase coordinateDirection a (fun y => ∑ l, ∑ k, F l k y) x = _
    rw [scalarSecondBase_fintype_sum _ _ _ hs x]
    apply Finset.sum_congr rfl
    intro l _
    exact scalarSecondBase_fintype_sum _ _ (F l) (hF l) x
  have hleft (l k : Fin 3) :
      directionalFDeriv (coordinateDirection k) (scalarSecondBase coordinateDirection a (d l)) x =
        ∑ i, ∑ j, directionalFDeriv (coordinateDirection k)
          (fun y => a y i j • directionalFDeriv (coordinateDirection i)
            (directionalFDeriv (coordinateDirection j) (d l)) y) x := by
    let H : Fin 3 → Fin 3 → R3 → E := fun i j y => a y i j •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) y
    have hH (i j : Fin 3) : ContDiff ℝ ∞ (H i j) := (ha i j).smul
      (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ _ (hd l)))
    change directionalFDeriv _ (fun y => ∑ i, ∑ j, H i j y) x = _
    rw [directionalFDeriv_fintype_sum _ _ (fun i => ContDiff.sum (fun j _ => hH i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact directionalFDeriv_fintype_sum _ (H i) (hH i) x
  unfold frameLoweringFirstPrincipalCommutator
  rw [hright]
  unfold frameLoweringFirst
  simp_rw [hleft,Finset.smul_sum]
  simp only [scalarSecondBase,F]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact lowering_directional_principal_commutator _ _ _ _ _ _ (ha i j) (hc l k) (hd l) x


/-- Actual real Hermitian symmetry and base commutation collect the full second-base
coefficient into the already defined p, with no collection identity as a premise. -/
theorem frameLoweringFirstPrincipalCommutator_collection (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hd : ∀ l, ContDiff ℝ ∞ (d l))
    (hsym : ∀ y, (a y).IsHermitian) (x : R3) :
    frameLoweringFirstPrincipalCommutator a c d x =
      framePrincipalSecondPart a c d x + framePrincipalFirstRemainder a c d x := by
  let U : E := ∑ l, ∑ k, ∑ i, ∑ j,
    (-(c l k x*directionalFDeriv (coordinateDirection k) (fun y => a y i j) x)) •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x
  let V : E := framePrincipalFirstRemainder a c d x
  let W : E := ∑ l, ∑ k, ∑ i, ∑ j,
    (a x i j*directionalFDeriv (coordinateDirection j) (c l k) x) •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection k) (d l)) x
  let Z : E := ∑ l, ∑ k, ∑ i, ∑ j,
    (a x i j*directionalFDeriv (coordinateDirection i) (c l k) x) •
      directionalFDeriv (coordinateDirection j) (directionalFDeriv (coordinateDirection k) (d l)) x
  have hsymm (i k : Fin 3) : a x k i = a x i k := by
    simpa only [star_trivial] using (hsym x).apply i k
  have hU : U = ∑ i, ∑ j, ∑ l, ∑ k,
      (-(c l k x*directionalFDeriv (coordinateDirection k) (fun y => a y i j) x)) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x :=
    sum_four_reorder_ijlk _
  have hW : W = ∑ i, ∑ j, ∑ l, ∑ k,
      (a x k i*directionalFDeriv (coordinateDirection k) (c l j) x) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x := by
    unfold W
    rw [sum_four_reorder_iklj]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [hsymm k i]
  have hZ : Z = ∑ i, ∑ j, ∑ l, ∑ k,
      (a x k j*directionalFDeriv (coordinateDirection k) (c l i) x) •
        directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x := by
    unfold Z
    rw [sum_four_reorder_kjli]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [directionalFDeriv_commute (coordinateDirection j) (coordinateDirection i) (d l) (hd l) x]
  have hp : framePrincipalSecondPart a c d x = U+W+Z := by
    rw [hU,hW,hZ]
    simp only [framePrincipalSecondPart,principalSecondFrameCoefficient,
      Finset.sum_smul,add_smul,Finset.sum_add_distrib]
  rw [frameLoweringFirstPrincipalCommutator_expansion a c d ha hc hd x]
  simp only [Finset.sum_add_distrib]
  change U+V+W+Z = framePrincipalSecondPart a c d x+V
  rw [hp]
  abel

/-- Actual frame and actual a=rQ instantiate the raw collection directly. -/
theorem actual_frameLoweringFirstPrincipalCommutator_collection
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (hhHerm : ∀ y, (h y).IsHermitian) (d : Fin 3 → R3 → E)
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (x : R3) :
    frameLoweringFirstPrincipalCommutator (actualPrincipalMatrix g L lam δ R p h)
      (fun l k y => referenceFrameEntryFamily g L l k (lam,y)) d x =
      framePrincipalSecondPart (actualPrincipalMatrix g L lam δ R p h)
        (fun l k y => referenceFrameEntryFamily g L l k (lam,y)) d x +
      framePrincipalFirstRemainder (actualPrincipalMatrix g L lam δ R p h)
        (fun l k y => referenceFrameEntryFamily g L l k (lam,y)) d x := by
  apply frameLoweringFirstPrincipalCommutator_collection
  · intro i j
    exact contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  · intro l k
    exact (contDiff_referenceFrameEntryFamily g hg L l k).comp
      (contDiff_const.prodMk contDiff_id)
  · exact hd
  · intro y
    exact actualPrincipalMatrix_isHermitian g hg L lam δ R p h y (hhHerm y)


/-- Coordinate raising first part T0. Angular outputs are constructed separately. -/
def frameRaisingFirst (c : Fin 3 → Fin 3 → R3 → ℝ) (r : Fin 3 → R3 → E)
    (x : R3) : E :=
  ∑ l, ∑ k, c l k x • directionalFDeriv (coordinateDirection k) (r l) x

/-- Density remains inside every base derivative of the natural coordinate T0 adjoint. -/
def frameRaisingFirstAdjoint (mu : R3 → ℝ) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (x : R3) : E :=
  ∑ l, ∑ k, (-((mu x)⁻¹)) • directionalFDeriv (coordinateDirection k)
    (fun y => (mu y*c l k y) • d l y) x

/-- Actual density/frame correction, distinct from scalar adjointZeroCoefficient. -/
def frameDensityCorrection (mu : R3 → ℝ) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (l : Fin 3) (x : R3) : ℝ :=
  (-((mu x)⁻¹)) * ∑ k, directionalFDeriv (coordinateDirection k) (fun y => mu y*c l k y) x

def frameDensityZero (mu : R3 → ℝ) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (x : R3) : E := ∑ l, frameDensityCorrection mu c l x • d l x

/-- Literal one-sided [T0 dagger,U2] on angular derivative outputs. -/
def rawCoordinateMixedLeft (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E) (x : R3) : E :=
  frameRaisingFirstAdjoint mu c (fun l => scalarSecondBase coordinateDirection a (d l)) x-
    scalarSecondBase coordinateDirection a (frameRaisingFirstAdjoint mu c d) x

/-- Literal adjoint partner [U2 dagger,T0] on angular raising outputs. -/
def rawCoordinateMixedRight (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (r : Fin 3 → R3 → E) (x : R3) : E :=
  scalarSecondBaseAdjoint coordinateDirection mu a (frameRaisingFirst c r) x-
    frameRaisingFirst c (fun l => scalarSecondBaseAdjoint coordinateDirection mu a (r l)) x

lemma frame_adjoint_term_coefficient (mu c : R3 → ℝ) (d : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (hp : ∀ y, mu y ≠ 0) (k : Fin 3) (x : R3) :
    (-((mu x)⁻¹)) • directionalFDeriv (coordinateDirection k)
      (fun y => (mu y*c y) • d y) x =
      (-c x) • directionalFDeriv (coordinateDirection k) d x+
      ((-((mu x)⁻¹))*directionalFDeriv (coordinateDirection k) (fun y => mu y*c y) x) • d x := by
  rw [directionalFDeriv_smul _ _ _ (hm.mul hc) hd,smul_add,smul_smul,smul_smul]
  have he : -((mu x)⁻¹)*(mu x*c x) = -c x := by
    field_simp [hp x]
  rw [he]
  exact add_comm _ _

lemma frameRaisingFirstAdjoint_coefficient_form (mu : R3 → ℝ)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hp : ∀ y, mu y ≠ 0) (x : R3) :
    frameRaisingFirstAdjoint mu c d x = frameLoweringFirst c d x+frameDensityZero mu c d x := by
  have ht (l k : Fin 3) := frame_adjoint_term_coefficient mu (c l k) (d l) hm (hc l k) (hd l) hp k x
  simp only [frameRaisingFirstAdjoint,ht,Finset.sum_add_distrib]
  simp only [frameLoweringFirst,frameDensityZero,frameDensityCorrection,
    Finset.mul_sum,Finset.sum_smul]

lemma contDiff_frameRaisingFirst (c : Fin 3 → Fin 3 → R3 → ℝ)
    (r : Fin 3 → R3 → E) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hr : ∀ l, ContDiff ℝ ∞ (r l)) : ContDiff ℝ ∞ (frameRaisingFirst c r) :=
  ContDiff.sum (fun l _ => ContDiff.sum (fun k _ =>
    (hc l k).smul (contDiff_directionalFDeriv _ _ (hr l))))

lemma contDiff_frameRaisingFirstAdjoint (mu : R3 → ℝ)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hp : ∀ y, mu y ≠ 0) :
    ContDiff ℝ ∞ (frameRaisingFirstAdjoint mu c d) :=
  ContDiff.sum (fun l _ => ContDiff.sum (fun k _ =>
    (hm.inv hp).neg.smul (contDiff_directionalFDeriv _ _ ((hm.mul (hc l k)).smul (hd l)))))

lemma hasCompactSupport_frameRaisingFirst (c : Fin 3 → Fin 3 → R3 → ℝ)
    (r : Fin 3 → R3 → E) (hr : ∀ l, HasCompactSupport (r l)) :
    HasCompactSupport (frameRaisingFirst c r) := by
  have ht := HasCompactSupport.finset_sum (s := Finset.univ) (fun l _ =>
    HasCompactSupport.finset_sum (s := Finset.univ) (fun k _ =>
      ((hr l).fderiv_apply (𝕜 := ℝ) (coordinateDirection k)).smul_left (f := c l k)))
  convert ht using 1
  funext x
  simp only [frameRaisingFirst,directionalFDeriv,Finset.sum_apply,Pi.smul_apply']

lemma hasCompactSupport_frameRaisingFirstAdjoint (mu : R3 → ℝ)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hd : ∀ l, HasCompactSupport (d l)) :
    HasCompactSupport (frameRaisingFirstAdjoint mu c d) := by
  have ht := HasCompactSupport.finset_sum (s := Finset.univ) (fun l _ =>
    HasCompactSupport.finset_sum (s := Finset.univ) (fun k _ =>
      (((hd l).smul_left (f := fun y => mu y*c l k y)).fderiv_apply
        (𝕜 := ℝ) (coordinateDirection k)).smul_left (f := fun y => -((mu y)⁻¹))))
  convert ht using 1
  funext x
  simp only [frameRaisingFirstAdjoint,directionalFDeriv,Finset.sum_apply,Pi.smul_apply',Pi.smul_def']


open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  AngularShiftGraph HarmonicDerivativeOperator BaseDensityAdjoint

/-- Fixed base differentiation preserves the genuine maximal raising graph. -/
lemma directionalFDeriv_sphereRaisingGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (X : R3) (u r : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ r)
    (hgraph : ∀ y, (u y,r y) ∈ sphereRaisingGraph hF hO hD l) (x : R3) :
    (directionalFDeriv X u x,directionalFDeriv X r x) ∈ sphereRaisingGraph hF hO hD l := by
  constructor
  · have he : (fun y => sphereHarmonicCoordinate hO hD 0 (r y)) = fun _ : R3 => 0 :=
      funext (fun y => (hgraph y).1)
    have hdiff := congrArg (fun f => fderiv ℝ f x X) he
    rw [directionalDeriv_fixed_clm _ X r hr x] at hdiff
    simpa only [fderiv_const_apply,ContinuousLinearMap.zero_apply,directionalFDeriv] using hdiff
  · intro m
    have he : (fun y => sphereHarmonicCoordinate hO hD (m+1) (r y)) =
        fun y => harmonicDerivativeAdjoint hF m l (sphereHarmonicCoordinate hO hD m (u y)) :=
      funext (fun y => (hgraph y).2 m)
    have hdiff := congrArg (fun f => fderiv ℝ f x X) he
    rw [directionalDeriv_fixed_clm _ X r hr x,
      directionalDeriv_fixed_clm (harmonicDerivativeAdjoint hF m l) X
        (fun y => sphereHarmonicCoordinate hO hD m (u y))
        ((sphereHarmonicCoordinate hO hD m).contDiff.comp hu) x,
      directionalDeriv_fixed_clm _ X u hu x] at hdiff
    exact hdiff

lemma second_directionalFDeriv_sphereRaisingGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (X Y : R3) (u r : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ r)
    (hgraph : ∀ y, (u y,r y) ∈ sphereRaisingGraph hF hO hD l) (x : R3) :
    (directionalFDeriv X (directionalFDeriv Y u) x,
      directionalFDeriv X (directionalFDeriv Y r) x) ∈ sphereRaisingGraph hF hO hD l :=
  directionalFDeriv_sphereRaisingGraph hF hO hD l X _ _
    (contDiff_directionalFDeriv Y u hu) (contDiff_directionalFDeriv Y r hr)
    (directionalFDeriv_sphereRaisingGraph hF hO hD l Y u r hu hr hgraph) x

lemma scalarSecondBase_sphereDerivativeGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (a : MatrixField) (u d : R3 → SphereL2) (hu : ContDiff ℝ ∞ u) (hd : ContDiff ℝ ∞ d)
    (hgraph : ∀ y, (u y,d y) ∈ sphereDerivativeGraph hF hO hD l) (x : R3) :
    (scalarSecondBase coordinateDirection a u x,scalarSecondBase coordinateDirection a d x) ∈
      sphereDerivativeGraph hF hO hD l := by
  intro m
  simp only [scalarSecondBase,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z => (a x i j) • z)
    (second_directionalDeriv_sphereDerivativeGraph hF hO hD l
      (coordinateDirection i) (coordinateDirection j) u d hu hd hgraph x m)

/-- The actual density adjoint also preserves the genuine raising graph. -/
lemma scalarSecondBaseAdjoint_sphereRaisingGraph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (mu : R3 → ℝ) (a : MatrixField) (u r : R3 → SphereL2)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ r)
    (hgraph : ∀ y, (u y,r y) ∈ sphereRaisingGraph hF hO hD l) (x : R3) :
    (scalarSecondBaseAdjoint coordinateDirection mu a u x,
      scalarSecondBaseAdjoint coordinateDirection mu a r x) ∈ sphereRaisingGraph hF hO hD l := by
  have hweighted (i j : Fin 3) (y : R3) :
      ((mu y*a y i j) • u y,(mu y*a y i j) • r y) ∈ sphereRaisingGraph hF hO hD l :=
    (sphereRaisingGraph hF hO hD l).smul_mem _ (hgraph y)
  have hsecond (i j : Fin 3) := second_directionalFDeriv_sphereRaisingGraph hF hO hD l
    (coordinateDirection j) (coordinateDirection i)
    (fun y => (mu y*a y i j) • u y) (fun y => (mu y*a y i j) • r y)
    ((hm.mul (ha i j)).smul hu) ((hm.mul (ha i j)).smul hr) (hweighted i j) x
  have hzero (i j : Fin 3) : sphereHarmonicCoordinate hO hD 0
      (directionalFDeriv (coordinateDirection j) (directionalFDeriv (coordinateDirection i)
        (fun y => (mu y*a y i j) • r y)) x) = 0 := (hsecond i j).1
  constructor
  · simp only [scalarSecondBaseAdjoint,map_smul,map_sum,hzero,Finset.sum_const_zero,smul_zero]
  · intro m
    simp only [scalarSecondBaseAdjoint,map_smul,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hsecond i j).2 m

lemma raising_derivative_inner_transport (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l : Fin 3)
    (X : R3) (u r w d : R3 → SphereL2)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ r)
    (hru : ∀ y, (u y,r y) ∈ sphereRaisingGraph hF hO hD l)
    (hdw : ∀ y, (w y,d y) ∈ sphereDerivativeGraph hF hO hD l) (x : R3) :
    ⟪directionalFDeriv X r x,w x⟫_ℝ = ⟪directionalFDeriv X u x,d x⟫_ℝ := by
  calc
    _ = ⟪w x,directionalFDeriv X r x⟫_ℝ := real_inner_comm _ _
    _ = ⟪d x,directionalFDeriv X u x⟫_ℝ :=
      (sphereDerivativeGraph_inner_adjoint hF hO hD l _ _ _ _ (hdw x)
        (directionalFDeriv_sphereRaisingGraph hF hO hD l X u r hu hr hru x)).symm
    _ = _ := real_inner_comm _ _

/-- Genuine compact adjunction of one coordinate raising term. -/
lemma compact_frameRaisingFirst_term_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (l k : Fin 3)
    (mu c : R3 → ℝ) (u r w d : R3 → SphereL2)
    (hm : ContDiff ℝ ∞ mu) (hc : ContDiff ℝ ∞ c)
    (hu : ContDiff ℝ ∞ u) (hr : ContDiff ℝ ∞ r) (hd : ContDiff ℝ ∞ d)
    (hcu : HasCompactSupport u) (hp : ∀ y, 0 < mu y)
    (hru : ∀ y, (u y,r y) ∈ sphereRaisingGraph hF hO hD l)
    (hdw : ∀ y, (w y,d y) ∈ sphereDerivativeGraph hF hO hD l) :
    (∫ x : R3, mu x*c x*⟪directionalFDeriv (coordinateDirection k) r x,w x⟫_ℝ) =
      ∫ x : R3, mu x*⟪u x,(-((mu x)⁻¹)) • directionalFDeriv (coordinateDirection k)
        (fun y => (mu y*c y) • d y) x⟫_ℝ := by
  have he : (fun x => mu x*c x*⟪directionalFDeriv (coordinateDirection k) r x,w x⟫_ℝ) =
      fun x => mu x*c x*⟪directionalFDeriv (coordinateDirection k) u x,d x⟫_ℝ :=
    funext (fun x => congrArg (fun t => mu x*c x*t)
      (raising_derivative_inner_transport hF hO hD l (coordinateDirection k) u r w d hu hr hru hdw x))
  rw [he]
  have h := compact_weighted_first_adjoint (coordinateDirection k) mu c u d hm hc hu hd hcu
  change (∫ x : R3, mu x*c x*⟪directionalFDeriv (coordinateDirection k) u x,d x⟫_ℝ) = _ at h
  rw [h,← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [real_inner_smul_right,real_inner_comm,mul_neg,← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (hp x)),one_mul,neg_one_mul,
    BaseDensityAdjoint.directionalDeriv,directionalFDeriv]

/-- Genuine compact adjunction of constructed coordinate T0 and its density adjoint. -/
theorem compact_frameRaisingFirst_adjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (mu : R3 → ℝ) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (u w : R3 → SphereL2) (r d : Fin 3 → R3 → SphereL2)
    (hm : ContDiff ℝ ∞ mu) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hu : ContDiff ℝ ∞ u) (hr : ∀ l, ContDiff ℝ ∞ (r l))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hcu : HasCompactSupport u) (hp : ∀ y, 0 < mu y)
    (hru : ∀ l y, (u y,r l y) ∈ sphereRaisingGraph hF hO hD l)
    (hdw : ∀ l y, (w y,d l y) ∈ sphereDerivativeGraph hF hO hD l) :
    (∫ x : R3, mu x*⟪frameRaisingFirst c r x,w x⟫_ℝ) =
      ∫ x : R3, mu x*⟪u x,frameRaisingFirstAdjoint mu c d x⟫_ℝ := by
  have hl (l k : Fin 3) : Integrable (fun x => mu x*c l k x*
      ⟪directionalFDeriv (coordinateDirection k) (r l) x,w x⟫_ℝ) := by
    have he : (fun x => mu x*c l k x*⟪directionalFDeriv (coordinateDirection k) (r l) x,w x⟫_ℝ) =
        fun x => ⟪(mu x*c l k x) • d l x,directionalFDeriv (coordinateDirection k) u x⟫_ℝ := by
      funext x
      rw [raising_derivative_inner_transport hF hO hD l _ u (r l) w (d l) hu (hr l) (hru l) (hdw l) x]
      simp only [real_inner_smul_left,real_inner_comm]
    rw [he]
    exact compact_inner_integrable _ _ ((hm.mul (hc l k)).smul (hd l)).continuous
      (contDiff_directionalFDeriv _ u hu).continuous (hcu.fderiv_apply (𝕜 := ℝ) _)
  have hrint (l k : Fin 3) : Integrable (fun x => mu x*⟪u x,
      (-((mu x)⁻¹)) • directionalFDeriv (coordinateDirection k)
        (fun y => (mu y*c l k y) • d l y) x⟫_ℝ) := by
    have he : (fun x => mu x*⟪u x,(-((mu x)⁻¹)) • directionalFDeriv (coordinateDirection k)
        (fun y => (mu y*c l k y) • d l y) x⟫_ℝ) =
        fun x => -⟪directionalFDeriv (coordinateDirection k)
          (fun y => (mu y*c l k y) • d l y) x,u x⟫_ℝ := by
      funext x
      simp only [real_inner_smul_right,real_inner_comm,mul_neg,← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (hp x)),one_mul,neg_one_mul]
    rw [he]
    exact (compact_inner_integrable _ u
      (contDiff_directionalFDeriv _ _ ((hm.mul (hc l k)).smul (hd l))).continuous
      hu.continuous hcu).neg
  simp only [frameRaisingFirst,frameRaisingFirstAdjoint,sum_inner,inner_sum,
    real_inner_smul_left,Finset.mul_sum,← mul_assoc]
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun k _ => hl l k)),
    integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun k _ => hrint l k))]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finsetSum _ (fun k _ => hl l k),integral_finsetSum _ (fun k _ => hrint l k)]
  apply Finset.sum_congr rfl
  intro k _
  exact compact_frameRaisingFirst_term_adjoint hF hO hD l k mu (c l k) u (r l) w (d l)
    hm (hc l k) hu (hr l) (hd l) hcu hp (hru l) (hdw l)


lemma contDiff_frameDensityCorrection (mu : R3 → ℝ)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (hm : ContDiff ℝ ∞ mu)
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hp : ∀ y, mu y ≠ 0) (l : Fin 3) :
    ContDiff ℝ ∞ (frameDensityCorrection mu c l) :=
  (hm.inv hp).neg.mul (ContDiff.sum (fun k _ =>
    contDiff_directionalFDeriv _ _ (hm.mul (hc l k))))

lemma contDiff_frameLoweringFirst (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) : ContDiff ℝ ∞ (frameLoweringFirst c d) :=
  ContDiff.sum (fun l _ => ContDiff.sum (fun k _ =>
    (hc l k).neg.smul (contDiff_directionalFDeriv _ _ (hd l))))

lemma contDiff_frameDensityZero (mu : R3 → ℝ) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (d : Fin 3 → R3 → E) (hm : ContDiff ℝ ∞ mu) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hp : ∀ y, mu y ≠ 0) :
    ContDiff ℝ ∞ (frameDensityZero mu c d) :=
  ContDiff.sum (fun l _ => (contDiff_frameDensityCorrection mu c hm hc hp l).smul (hd l))

/-- The remaining density/frame commutator has literal first and zero base terms. -/
def frameDensityPrincipalRemainder (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E) (x : R3) : E :=
  ∑ l, ∑ i, ∑ j, (
    -(a x i j*directionalFDeriv (coordinateDirection i)
      (directionalFDeriv (coordinateDirection j) (frameDensityCorrection mu c l)) x) • d l x-
    (a x i j*directionalFDeriv (coordinateDirection j) (frameDensityCorrection mu c l) x) •
      directionalFDeriv (coordinateDirection i) (d l) x-
    (a x i j*directionalFDeriv (coordinateDirection i) (frameDensityCorrection mu c l) x) •
      directionalFDeriv (coordinateDirection j) (d l) x)

lemma frameDensityZero_principal_commutator (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hc : ∀ l k, ContDiff ℝ ∞ (c l k))
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hp : ∀ y, mu y ≠ 0) (x : R3) :
    frameDensityZero mu c (fun l => scalarSecondBase coordinateDirection a (d l)) x-
      scalarSecondBase coordinateDirection a (frameDensityZero mu c d) x =
        frameDensityPrincipalRemainder mu a c d x := by
  let F : Fin 3 → R3 → E := fun l y => frameDensityCorrection mu c l y • d l y
  have hF (l : Fin 3) : ContDiff ℝ ∞ (F l) :=
    (contDiff_frameDensityCorrection mu c hm hc hp l).smul (hd l)
  have hright : scalarSecondBase coordinateDirection a (frameDensityZero mu c d) x =
      ∑ l, scalarSecondBase coordinateDirection a (F l) x :=
    scalarSecondBase_fintype_sum _ _ _ hF x
  rw [hright]
  simp only [frameDensityZero,scalarSecondBase,Finset.smul_sum,frameDensityPrincipalRemainder]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact scalar_zero_second_commutator _ _ (fun y => a y i j) (frameDensityCorrection mu c l)
    (d l) (contDiff_frameDensityCorrection mu c hm hc hp l) (hd l) x

/-- Complete literal one-sided coordinate T0/principal collection. All lower terms remain explicit. -/
theorem rawCoordinateMixedLeft_collection (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hd : ∀ l, ContDiff ℝ ∞ (d l))
    (hp : ∀ y, mu y ≠ 0) (hsym : ∀ y, (a y).IsHermitian) (x : R3) :
    rawCoordinateMixedLeft mu a c d x = framePrincipalSecondPart a c d x+
      framePrincipalFirstRemainder a c d x+frameDensityPrincipalRemainder mu a c d x := by
  have hsd (l : Fin 3) : ContDiff ℝ ∞ (scalarSecondBase coordinateDirection a (d l)) :=
    contDiff_scalarSecondBase _ _ _ ha (hd l)
  have he : frameRaisingFirstAdjoint mu c d = fun y => frameLoweringFirst c d y+frameDensityZero mu c d y :=
    funext (frameRaisingFirstAdjoint_coefficient_form mu c d hm hc hd hp)
  unfold rawCoordinateMixedLeft
  rw [frameRaisingFirstAdjoint_coefficient_form mu c _ hm hc hsd hp x,he,
    scalarSecondBase_add _ _ _ _ (contDiff_frameLoweringFirst c d hc hd)
      (contDiff_frameDensityZero mu c d hm hc hd hp)]
  have hfirst := frameLoweringFirstPrincipalCommutator_collection a c d ha hc hd hsym x
  have hzero := frameDensityZero_principal_commutator mu a c d hm hc hd hp x
  unfold frameLoweringFirstPrincipalCommutator at hfirst
  rw [← hfirst,← hzero]
  abel


lemma weighted_compact_pair_integrable (mu : R3 → ℝ) (F u : R3 → E)
    (hm : ContDiff ℝ ∞ mu) (hF : ContDiff ℝ ∞ F) (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) : Integrable (fun x => mu x*⟪F x,u x⟫_ℝ) := by
  simpa only [real_inner_smul_left] using
    compact_inner_integrable (fun x => mu x • F x) u (hm.smul hF).continuous hu.continuous hcu

lemma contDiff_rawCoordinateMixedLeft (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hd : ∀ l, ContDiff ℝ ∞ (d l))
    (hp : ∀ y, mu y ≠ 0) : ContDiff ℝ ∞ (rawCoordinateMixedLeft mu a c d) :=
  (contDiff_frameRaisingFirstAdjoint mu c _ hm hc
    (fun l => contDiff_scalarSecondBase _ _ _ ha (hd l)) hp).sub
    (contDiff_scalarSecondBase _ _ _ ha (contDiff_frameRaisingFirstAdjoint mu c d hm hc hd hp))

lemma contDiff_rawCoordinateMixedRight (mu : R3 → ℝ) (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (r : Fin 3 → R3 → E)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hr : ∀ l, ContDiff ℝ ∞ (r l))
    (hp : ∀ y, mu y ≠ 0) : ContDiff ℝ ∞ (rawCoordinateMixedRight mu a c r) :=
  (contDiff_scalarSecondBaseAdjoint _ _ _ _ hm ha (contDiff_frameRaisingFirst c r hc hr) hp).sub
    (contDiff_frameRaisingFirst c _ hc (fun l =>
      contDiff_scalarSecondBaseAdjoint _ _ _ _ hm ha (hr l) hp))

/-- The genuine compact adjoint partner has the same real quadratic form. -/
theorem compact_rawCoordinateMixed_adjoint_partner (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (mu : R3 → ℝ) (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (u : R3 → SphereL2) (d r : Fin 3 → R3 → SphereL2)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hu : ContDiff ℝ ∞ u)
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hr : ∀ l, ContDiff ℝ ∞ (r l))
    (hcu : HasCompactSupport u) (hcd : ∀ l, HasCompactSupport (d l))
    (hp : ∀ y, 0 < mu y)
    (hdgraph : ∀ l y, (u y,d l y) ∈ sphereDerivativeGraph hF hO hD l)
    (hrgraph : ∀ l y, (u y,r l y) ∈ sphereRaisingGraph hF hO hD l) :
    (∫ x : R3, mu x*⟪rawCoordinateMixedRight mu a c r x,u x⟫_ℝ) =
      ∫ x : R3, mu x*⟪rawCoordinateMixedLeft mu a c d x,u x⟫_ℝ := by
  let S := scalarSecondBase coordinateDirection a u
  let SA := scalarSecondBaseAdjoint coordinateDirection mu a u
  let T := frameRaisingFirst c r
  let TA := frameRaisingFirstAdjoint mu c d
  let Sd := fun l => scalarSecondBase coordinateDirection a (d l)
  let SAr := fun l => scalarSecondBaseAdjoint coordinateDirection mu a (r l)
  have hp0 (y : R3) : mu y ≠ 0 := ne_of_gt (hp y)
  have hS : ContDiff ℝ ∞ S := contDiff_scalarSecondBase _ _ _ ha hu
  have hSA : ContDiff ℝ ∞ SA := contDiff_scalarSecondBaseAdjoint _ _ _ _ hm ha hu hp0
  have hT : ContDiff ℝ ∞ T := contDiff_frameRaisingFirst c r hc hr
  have hTA : ContDiff ℝ ∞ TA := contDiff_frameRaisingFirstAdjoint mu c d hm hc hd hp0
  have hSd (l : Fin 3) : ContDiff ℝ ∞ (Sd l) := contDiff_scalarSecondBase _ _ _ ha (hd l)
  have hSAr (l : Fin 3) : ContDiff ℝ ∞ (SAr l) :=
    contDiff_scalarSecondBaseAdjoint _ _ _ _ hm ha (hr l) hp0
  have hcSA : HasCompactSupport SA := hasCompactSupport_scalarSecondBaseAdjoint _ _ _ _ hcu
  have hcTA : HasCompactSupport TA := hasCompactSupport_frameRaisingFirstAdjoint mu c d hcd
  have h1 := compact_frameRaisingFirst_adjoint hF hO hD mu c u S r Sd
    hm hc hu hr hSd hcu hp hrgraph
    (fun l => scalarSecondBase_sphereDerivativeGraph hF hO hD l a u (d l) hu (hd l) (hdgraph l))
  have h2 := compact_scalarSecondBase_adjoint coordinateDirection mu a TA u hm ha hTA hu hcTA hp
  have h3 := compact_scalarSecondBase_adjoint coordinateDirection mu a u T hm ha hu hT hcu hp
  have h4 := compact_frameRaisingFirst_adjoint hF hO hD mu c SA u SAr d
    hm hc hSA hSAr hd hcSA hp
    (fun l => scalarSecondBaseAdjoint_sphereRaisingGraph hF hO hD l mu a u (r l)
      hm ha hu (hr l) (hrgraph l)) hdgraph
  have hl1 := weighted_compact_pair_integrable mu (frameRaisingFirstAdjoint mu c Sd) u hm
    (contDiff_frameRaisingFirstAdjoint mu c Sd hm hc hSd hp0) hu hcu
  have hl2 := weighted_compact_pair_integrable mu (scalarSecondBase coordinateDirection a TA) u hm
    (contDiff_scalarSecondBase _ _ _ ha hTA) hu hcu
  have hr1 := weighted_compact_pair_integrable mu (scalarSecondBaseAdjoint coordinateDirection mu a T) u hm
    (contDiff_scalarSecondBaseAdjoint _ _ _ _ hm ha hT hp0) hu hcu
  have hr2 := weighted_compact_pair_integrable mu (frameRaisingFirst c SAr) u hm
    (contDiff_frameRaisingFirst c SAr hc hSAr) hu hcu
  change (∫ x, mu x*⟪scalarSecondBaseAdjoint coordinateDirection mu a T x-
    frameRaisingFirst c SAr x,u x⟫_ℝ) =
      ∫ x, mu x*⟪frameRaisingFirstAdjoint mu c Sd x-scalarSecondBase coordinateDirection a TA x,u x⟫_ℝ
  simp only [inner_sub_left,mul_sub]
  rw [integral_sub hr1 hr2,integral_sub hl1 hl2]
  have he1 : (∫ x : R3, mu x*⟪scalarSecondBaseAdjoint coordinateDirection mu a T x,u x⟫_ℝ) =
      ∫ x : R3, mu x*⟪frameRaisingFirstAdjoint mu c Sd x,u x⟫_ℝ := by
    calc
      _ = ∫ x : R3, mu x*⟪u x,scalarSecondBaseAdjoint coordinateDirection mu a T x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [real_inner_comm]
      _ = ∫ x : R3, mu x*⟪S x,T x⟫_ℝ := h3.symm
      _ = ∫ x : R3, mu x*⟪T x,S x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [real_inner_comm]
      _ = ∫ x : R3, mu x*⟪u x,frameRaisingFirstAdjoint mu c Sd x⟫_ℝ := h1
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [real_inner_comm]
  have he2 : (∫ x : R3, mu x*⟪frameRaisingFirst c SAr x,u x⟫_ℝ) =
      ∫ x : R3, mu x*⟪scalarSecondBase coordinateDirection a TA x,u x⟫_ℝ := by
    calc
      _ = ∫ x : R3, mu x*⟪SA x,TA x⟫_ℝ := h4
      _ = ∫ x : R3, mu x*⟪TA x,SA x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [real_inner_comm]
      _ = _ := h2.symm
  rw [he1,he2]

/-- Exact source factor: 2[T0 dagger,U2]+2[U2 dagger,T0] gives four times the left form. -/
theorem compact_rawCoordinateMixed_source_pair (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (mu : R3 → ℝ) (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (u : R3 → SphereL2) (d r : Fin 3 → R3 → SphereL2)
    (hm : ContDiff ℝ ∞ mu) (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hu : ContDiff ℝ ∞ u)
    (hd : ∀ l, ContDiff ℝ ∞ (d l)) (hr : ∀ l, ContDiff ℝ ∞ (r l))
    (hcu : HasCompactSupport u) (hcd : ∀ l, HasCompactSupport (d l))
    (hp : ∀ y, 0 < mu y)
    (hdgraph : ∀ l y, (u y,d l y) ∈ sphereDerivativeGraph hF hO hD l)
    (hrgraph : ∀ l y, (u y,r l y) ∈ sphereRaisingGraph hF hO hD l) :
    (∫ x : R3, mu x*⟪(2 : ℝ) • rawCoordinateMixedLeft mu a c d x+
      (2 : ℝ) • rawCoordinateMixedRight mu a c r x,u x⟫_ℝ) =
      4*(∫ x : R3, mu x*⟪rawCoordinateMixedLeft mu a c d x,u x⟫_ℝ) := by
  have hp0 (y : R3) : mu y ≠ 0 := ne_of_gt (hp y)
  have hl := weighted_compact_pair_integrable mu _ u hm
    (contDiff_rawCoordinateMixedLeft mu a c d hm ha hc hd hp0) hu hcu
  have hrint := weighted_compact_pair_integrable mu _ u hm
    (contDiff_rawCoordinateMixedRight mu a c r hm ha hc hr hp0) hu hcu
  simp only [inner_add_left,real_inner_smul_left,mul_add]
  have he (F : R3 → SphereL2) (x : R3) : mu x*(2*⟪F x,u x⟫_ℝ) =
      2*(mu x*⟪F x,u x⟫_ℝ) := by ring
  simp_rw [he]
  rw [integral_add (hl.const_mul 2) (hrint.const_mul 2),integral_const_mul,integral_const_mul,
    compact_rawCoordinateMixed_adjoint_partner hF hO hD mu a c u d r hm ha hc hu hd hr hcu hcd hp hdgraph hrgraph]
  ring


open SmoothSphereFields AmbientAngularShift AmbientPrincipalSecondIntegration
  PerturbedDensityAdjoint ConformalDepth

/-- The actual coordinate T0/principal left piece on constructed ambient angular fields. -/
def actualAmbientMixedLeft (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  rawCoordinateMixedLeft (fun x => referenceDensityFamily g L (lam,x))
    (actualPrincipalMatrix g L lam δ R p h)
    (fun l k x => referenceFrameEntryFamily g L l k (lam,x))
    (fun l => ambientDerivativeField hF hO hD l G hG)

/-- The actual coordinate T0/principal right piece, retaining the genuine density adjoint. -/
def actualAmbientMixedRight (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  rawCoordinateMixedRight (fun x => referenceDensityFamily g L (lam,x))
    (actualPrincipalMatrix g L lam δ R p h)
    (fun l k x => referenceFrameEntryFamily g L l k (lam,x))
    (fun l => ambientRaisingField hF hO hD l G hG)

/-- All graph, smoothness, support and density inputs are discharged on actual ambient fields. -/
theorem actual_ambient_mixed_source_pair (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*⟪
      (2 : ℝ) • actualAmbientMixedLeft hF hO hD g L lam δ R p h G hG x+
      (2 : ℝ) • actualAmbientMixedRight hF hO hD g L lam δ R p h G hG x,
      ambientSphereL2 G hG x⟫_ℝ) =
      4*(∫ x : R3, referenceDensityFamily g L (lam,x)*
        ⟪actualAmbientMixedLeft hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) := by
  apply compact_rawCoordinateMixed_source_pair hF hO hD
  · exact (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  · exact contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  · intro l k
    exact (contDiff_referenceFrameEntryFamily g hg L l k).comp (contDiff_const.prodMk contDiff_id)
  · exact contDiff_ambientSphereL2 G hG
  · intro l
    exact contDiff_ambientDerivativeField hF hO hD l G hG
  · intro l
    exact contDiff_ambientRaisingField hF hO hD l G hG
  · exact HasCompactSupport.intro hK (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))
  · intro l
    exact hasCompactSupport_ambientDerivativeField hF hO hD l G hG K hK hz
  · intro y
    exact referenceDensityFamily_pos g hg L (lam,y)
  · exact fun l => ambientDerivativeField_graph hF hO hD l G hG
  · exact fun l => ambientRaisingField_graph hF hO hD l G hG

/-- The raw ambient left piece uses precisely the existing actual p and literal lower remainders. -/
theorem actual_ambient_mixed_left_collection (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (hhHerm : ∀ y, (h y).IsHermitian)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    actualAmbientMixedLeft hF hO hD g L lam δ R p h G hG x =
      framePrincipalSecondPart (actualPrincipalMatrix g L lam δ R p h)
        (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
        (fun l => ambientDerivativeField hF hO hD l G hG) x+
      framePrincipalFirstRemainder (actualPrincipalMatrix g L lam δ R p h)
        (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
        (fun l => ambientDerivativeField hF hO hD l G hG) x+
      frameDensityPrincipalRemainder (fun y => referenceDensityFamily g L (lam,y))
        (actualPrincipalMatrix g L lam δ R p h)
        (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
        (fun l => ambientDerivativeField hF hO hD l G hG) x := by
  apply rawCoordinateMixedLeft_collection
  · exact (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  · exact contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh
  · intro l k
    exact (contDiff_referenceFrameEntryFamily g hg L l k).comp (contDiff_const.prodMk contDiff_id)
  · intro l
    exact contDiff_ambientDerivativeField hF hO hD l G hG
  · intro y
    exact ne_of_gt (referenceDensityFamily_pos g hg L (lam,y))
  · intro y
    exact actualPrincipalMatrix_isHermitian g hg L lam δ R p h y (hhHerm y)

/-- Exactly the paired factor-four principal p quadratic contribution. -/
def actualAmbientPairedPrincipalForm (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : ℝ :=
  ∫ x : R3, referenceDensityFamily g L (lam,x)*⟪(4 : ℝ) •
    framePrincipalSecondPart (actualPrincipalMatrix g L lam δ R p h)
      (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
      (fun l => ambientDerivativeField hF hO hD l G hG) x,ambientSphereL2 G hG x⟫_ℝ

/-- Identification with the raw per-slot p forms, before applying their checked estimate. -/
theorem actual_ambient_paired_principal_form_eq (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) :
    actualAmbientPairedPrincipalForm hF hO hD g L lam δ R p h G hG =
      4*∑ i : Fin 3, ∑ j : Fin 3, ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG i j := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let a := actualPrincipalMatrix g L lam δ R p h
  let c := fun l k x => referenceFrameEntryFamily g L l k (lam,x)
  let d := fun l => ambientDerivativeField hF hO hD l G hG
  let u := ambientSphereL2 G hG
  let F : Fin 3 → Fin 3 → R3 → SphereL2 := fun i j x => ∑ l,
    principalSecondFrameCoefficient a c i j l x •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (d l)) x
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun y => a y i j) :=
    contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hc (l k : Fin 3) : ContDiff ℝ ∞ (c l k) :=
    (contDiff_referenceFrameEntryFamily g hg L l k).comp (contDiff_const.prodMk contDiff_id)
  have hd (l : Fin 3) : ContDiff ℝ ∞ (d l) := contDiff_ambientDerivativeField hF hO hD l G hG
  have hu : ContDiff ℝ ∞ u := contDiff_ambientSphereL2 G hG
  have hcu : HasCompactSupport u :=
    HasCompactSupport.intro hK (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))
  have hF (i j : Fin 3) : ContDiff ℝ ∞ (F i j) := ContDiff.sum (fun l _ =>
    (contDiff_principalSecondFrameCoefficient a c ha hc i j l).smul
      (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ _ (hd l))))
  have hint (i j : Fin 3) := weighted_compact_pair_integrable mu (F i j) u hm (hF i j) hu hcu
  have he : (fun x => mu x*⟪(4 : ℝ) • framePrincipalSecondPart a c d x,u x⟫_ℝ) =
      fun x => 4*(∑ i, ∑ j, mu x*⟪F i j x,u x⟫_ℝ) := by
    funext x
    simp only [framePrincipalSecondPart,F,sum_inner,real_inner_smul_left,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  change (∫ x, mu x*⟪(4 : ℝ) • framePrincipalSecondPart a c d x,u x⟫_ℝ) = _
  rw [he,integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  rfl

/-- Uniform actual paired-p estimate: the source factor four costs another fixed factor two.
No coefficient/form estimate is a new premise; the existing actual estimate is applied. -/
theorem exists_actual_ambient_paired_principal_form_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 →
      ∀ h : MatrixField, (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ x ∈ K, ∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δ R p L x)) →
      (∀ x ∈ K, 1 ≤ referenceProfileNorm g lam δ R p L x) →
      (∀ x ∈ K, referenceRadius δ R p L x*(referenceProfileNorm g lam δ R p L x)^2 ≤ eps) →
      ∀ G : R3 × R3 → ℝ, ∀ hG : ContDiff ℝ ∞ G,
      (∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) →
      |actualAmbientPairedPrincipalForm hF hO hD g L lam δ R p h G hG| ≤
        C*eps*ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG := by
  obtain ⟨C,hC,hbound⟩ := exists_ambient_principal_second_form_bound hF hO hD g hg L hL K hK
  refine ⟨36*C,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz
  have ht := (hbound lam hlam δ hδ hδ1 R hR p hp eps heps heps1 h hh hhjet hb hsmall G hG hz).2
  rw [actual_ambient_paired_principal_form_eq hF hO hD g hg L lam δ R p h hδ hR hh G hG K hK hz]
  calc
    _ = 2*|2*∑ i : Fin 3, ∑ j : Fin 3, ambientPrincipalSecondForm hF hO hD g L lam δ R p h G hG i j| := by
      rw [← abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),← abs_mul]
      congr 1
      ring
    _ ≤ 2*((18*C)*eps*ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = (36*C)*eps*ambientPrincipalSourceNormSquare hO hD g L lam δ R p G hG := by ring


/-- Actual p transpose into the already constructed raising field, with all ordered slots. -/
theorem actual_ambient_principal_second_transpose (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ⟪framePrincipalSecondPart (actualPrincipalMatrix g L lam δ R p h)
      (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
      (fun l => ambientDerivativeField hF hO hD l G hG) x,ambientSphereL2 G hG x⟫_ℝ =
      ∑ i, ∑ j, ⟪directionalFDeriv (coordinateDirection i)
        (directionalFDeriv (coordinateDirection j) (ambientSphereL2 G hG)) x,
        actualPrincipalSecondAdjointField g L lam δ R p h
          (fun l => ambientRaisingField hF hO hD l G hG) i j x⟫_ℝ := by
  simp only [framePrincipalSecondPart,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have htranspose := actual_principal_second_transpose hF hO hD g L lam δ R p h
    (ambientSphereL2 G hG) (fun l => ambientDerivativeField hF hO hD l G hG)
    (fun l => ambientRaisingField hF hO hD l G hG)
    (contDiff_ambientSphereL2 G hG) (fun l => contDiff_ambientDerivativeField hF hO hD l G hG)
    (fun l => ambientDerivativeField_graph hF hO hD l G hG)
    (fun l => ambientRaisingField_graph hF hO hD l G hG) i j x
  have hdir (X : R3) (w : R3 → SphereL2) :
      BaseDensityAdjoint.directionalDeriv X w = directionalFDeriv X w := rfl
  simpa only [hdir,sum_inner,actualPrincipalSecondFrameCoefficient] using htranspose

/-- The very same transpose has the existing actual balanced inverse-half graph. -/
theorem actual_ambient_principal_second_balanced_graph (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (i j : Fin 3) (x : R3) :
    (actualPrincipalSecondAdjointField g L lam δ R p h
      (fun l => ambientRaisingField hF hO hD l G hG) i j x,
      actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j x
        (ambientBesselField hO hD (1/2) (by norm_num) G hG x)) ∈
      sphereBesselGraph hO hD (-(1/2)) :=
  actualPrincipalSecondAdjointField_inverse_half_graph hF hO hD g L lam δ R p h
    (ambientSphereL2 G hG) (ambientBesselField hO hD (1/2) (by norm_num) G hG)
    (fun l => ambientRaisingField hF hO hD l G hG)
    (ambientBesselField_graph hO hD (1/2) (by norm_num) G hG)
    (fun l => ambientRaisingField_graph hF hO hD l G hG) i j x

lemma contDiff_framePrincipalSecondPart (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (d : Fin 3 → R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (hd : ∀ l, ContDiff ℝ ∞ (d l)) :
    ContDiff ℝ ∞ (framePrincipalSecondPart a c d) :=
  ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => ContDiff.sum (fun l _ =>
    (contDiff_principalSecondFrameCoefficient a c ha hc i j l).smul
      (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ _ (hd l))))))

/-- Literal lower part, retaining frame Hessians and density/frame rho derivatives. -/
def actualAmbientMixedLowerRemainder (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) : SphereL2 :=
  framePrincipalFirstRemainder (actualPrincipalMatrix g L lam δ R p h)
    (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
    (fun l => ambientDerivativeField hF hO hD l G hG) x+
  frameDensityPrincipalRemainder (fun y => referenceDensityFamily g L (lam,y))
    (actualPrincipalMatrix g L lam δ R p h)
    (fun l k y => referenceFrameEntryFamily g L l k (lam,y))
    (fun l => ambientDerivativeField hF hO hD l G hG) x

/-- Full selected coordinate source pair equals the paired p form plus literal lower remainders.
The theorem neither identifies T0 with full T nor asserts the remaining E bound. -/
theorem actual_ambient_mixed_source_collection (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (hδ : 0 < δ) (hR : 0 < R)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (hhHerm : ∀ y, (h y).IsHermitian)
    (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val) = 0) :
    (∫ x : R3, referenceDensityFamily g L (lam,x)*⟪
      (2 : ℝ) • actualAmbientMixedLeft hF hO hD g L lam δ R p h G hG x+
      (2 : ℝ) • actualAmbientMixedRight hF hO hD g L lam δ R p h G hG x,
      ambientSphereL2 G hG x⟫_ℝ) =
      actualAmbientPairedPrincipalForm hF hO hD g L lam δ R p h G hG+
      4*(∫ x : R3, referenceDensityFamily g L (lam,x)*
        ⟪actualAmbientMixedLowerRemainder hF hO hD g L lam δ R p h G hG x,ambientSphereL2 G hG x⟫_ℝ) := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (lam,x)
  let a := actualPrincipalMatrix g L lam δ R p h
  let c := fun l k x => referenceFrameEntryFamily g L l k (lam,x)
  let d := fun l => ambientDerivativeField hF hO hD l G hG
  let u := ambientSphereL2 G hG
  let P := framePrincipalSecondPart a c d
  let M := actualAmbientMixedLeft hF hO hD g L lam δ R p h G hG
  let V := actualAmbientMixedLowerRemainder hF hO hD g L lam δ R p h G hG
  have hm : ContDiff ℝ ∞ mu :=
    (contDiff_referenceDensityFamily g hg L).comp (contDiff_const.prodMk contDiff_id)
  have ha (i j : Fin 3) : ContDiff ℝ ∞ (fun y => a y i j) :=
    contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
  have hc (l k : Fin 3) : ContDiff ℝ ∞ (c l k) :=
    (contDiff_referenceFrameEntryFamily g hg L l k).comp (contDiff_const.prodMk contDiff_id)
  have hd (l : Fin 3) : ContDiff ℝ ∞ (d l) := contDiff_ambientDerivativeField hF hO hD l G hG
  have hu : ContDiff ℝ ∞ u := contDiff_ambientSphereL2 G hG
  have hcu : HasCompactSupport u :=
    HasCompactSupport.intro hK (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))
  have hP : ContDiff ℝ ∞ P := contDiff_framePrincipalSecondPart a c d ha hc hd
  have hM : ContDiff ℝ ∞ M := contDiff_rawCoordinateMixedLeft mu a c d hm ha hc hd
    (fun y => ne_of_gt (referenceDensityFamily_pos g hg L (lam,y)))
  have he (x : R3) : M x = P x+V x := by
    have ht := actual_ambient_mixed_left_collection hF hO hD g hg L lam δ R p h hδ hR hh hhHerm G hG x
    change M x = P x+framePrincipalFirstRemainder a c d x+frameDensityPrincipalRemainder mu a c d x at ht
    change M x = P x+(framePrincipalFirstRemainder a c d x+frameDensityPrincipalRemainder mu a c d x)
    simpa only [add_assoc] using ht
  have hV : ContDiff ℝ ∞ V := by
    have hve : V = fun x => M x-P x := by
      funext x
      rw [he]
      abel
    rw [hve]
    exact hM.sub hP
  have hintP := weighted_compact_pair_integrable mu P u hm hP hu hcu
  have hintV := weighted_compact_pair_integrable mu V u hm hV hu hcu
  have hpform : actualAmbientPairedPrincipalForm hF hO hD g L lam δ R p h G hG =
      4*(∫ x : R3, mu x*⟪P x,u x⟫_ℝ) := by
    change (∫ x : R3, mu x*⟪(4 : ℝ) • P x,u x⟫_ℝ) = _
    have hfun : (fun x => mu x*⟪(4 : ℝ) • P x,u x⟫_ℝ) =
        fun x => 4*(mu x*⟪P x,u x⟫_ℝ) := by
      funext x
      rw [real_inner_smul_left]
      ring
    rw [hfun,integral_const_mul]
  rw [actual_ambient_mixed_source_pair hF hO hD g hg L lam δ R p h hδ hR hh G hG K hK hz,hpform]
  change 4*(∫ x : R3, mu x*⟪M x,u x⟫_ℝ) = _
  simp_rw [he,inner_add_left,mul_add]
  rw [integral_add hintP hintV]
  ring

end OAI.AnisotropicCalderon.ActualRawMixedPrincipalCollection
