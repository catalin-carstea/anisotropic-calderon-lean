import Calderon.ActualDefectNorm
import Calderon.NaturalAdjointNormalForm
import Calderon.BalancedFrameAngularShift

set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualPrincipalErrorCoefficient
open PrincipalCommutator ScalarBaseAdjoint ReferenceDensityBounds PerturbedDensityAdjoint
  ConformalDepth ActualScalarPrincipalAdjoint ActualPerturbedDefect SmoothMetricFrame
  NaturalAngularAdjoint

/-- Actual orthonormal-frame coefficient, with physical coordinate k. -/
def referenceFrameEntryFamily (g : MatrixField) (L : ℝ) (l k : Fin 3)
    (z : ℝ × R3) : ℝ := referenceMetricGramFrame g L z l k

lemma contDiff_referenceFrameEntryFamily (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (l k : Fin 3) : ContDiff ℝ ∞ (referenceFrameEntryFamily g L l k) :=
  (contDiff_piLp_apply (p := 2) (i := k) :
    ContDiff ℝ ∞ (fun v : R3 => v k)).comp (contDiff_referenceMetricGramFrame g hg L l)

/-- Compactness of the actual geometry selects all frame two-jet constants before shrinkage. -/
theorem exists_referenceFrame_uniform_two_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ F : ℝ, 1 ≤ F ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ l k : Fin 3, ∀ s : JetTag,
      |coordinateJetFamily (referenceFrameEntryFamily g L l k) s (lam,x)| ≤ F := by
  obtain ⟨F,hF,hbound⟩ := exists_uniform_bound_finite_family
    (fun t : (Fin 3 × Fin 3) × JetTag =>
      coordinateJetFamily (referenceFrameEntryFamily g L t.1.1 t.1.2) t.2)
    (fun t => continuous_coordinateJetFamily _
      (contDiff_referenceFrameEntryFamily g hg L t.1.1 t.1.2) t.2) K hK
  exact ⟨F,hF,fun lam hlam x hx l k s => hbound lam hlam x hx ((l,k),s)⟩

/-- Unweighted actual a=rQ jets, derived using the actual radius and q=gamma inverse. -/
theorem exists_actual_principal_uniform_two_jet_bound (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ C0 C1 C2 : ℝ, 0 < C0 ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j k l,
        |actualPrincipalMatrix g L lam δ R p h x i j| ≤ C0 * eps / beta^2 ∧
        |directionalFDeriv (coordinateDirection k)
          (fun y => actualPrincipalMatrix g L lam δ R p h y i j) x| ≤ C1 * eps / beta ∧
        |directionalFDeriv (coordinateDirection l) (directionalFDeriv (coordinateDirection k)
          (fun y => actualPrincipalMatrix g L lam δ R p h y i j)) x| ≤ C2 * eps := by
  obtain ⟨M,hM,hbackground⟩ := exists_referenceBackground_uniform_two_jet_bound g hg L K hK
  obtain ⟨J1,hJ1,hjet1⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 1
  obtain ⟨J2,hJ2,hjet2⟩ := exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
    g hg L hL K hK 2
  refine ⟨M+1,(J1+2)*M*(M+1),(J2+4*J1+4)*M*(M+1),
    by positivity,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i j k l
  let r : R3 → ℝ := referenceRadius δ R p L
  let q : R3 → ℝ := fun y => referenceInverseEntryFamily g L i j (lam,y)
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hq : ContDiff ℝ ∞ q := (contDiff_referenceInverseEntryFamily g hg L i j).comp hslice
  have hqq : TwoJetBound (coordinateDirection k) (coordinateDirection l) q x M := by
    refine ⟨?_,?_,?_,?_⟩
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inl ())
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl k))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inl l))
    · exact hbackground lam hlam x hx (.inr (i,j)) (.inr (.inr (k,l)))
  have hr : ContDiff ℝ ∞ r := contDiff_referenceRadius_actual δ R p L hδ hR
  have hrpos : 0 < r x := referenceRadius_pos δ R p L x hδ hR
  have hbeta : 0 < beta := by linarith
  have hre : r x ≤ eps := by nlinarith [sq_nonneg (beta-1)]
  have hepr : eps*r x ≤ 1 := by nlinarith
  have hsum : |q x+h x i j| ≤ M+1 :=
    (abs_add_le _ _).trans (add_le_add hqq.1 ((hhjet i j k l).1.trans hepr))
  have ha0 : |actualPrincipalMatrix g L lam δ R p h x i j| ≤ (M+1)*eps/beta^2 := by
    have hrsmall : r x ≤ eps/beta^2 := (le_div_iff₀ (sq_pos_of_pos hbeta)).mpr hsmall
    calc
      _ = r x * |q x+h x i j| := by
        change |r x * (q x+h x i j)| = _
        rw [abs_mul,abs_of_pos hrpos]
      _ ≤ r x*(M+1) := mul_le_mul_of_nonneg_left hsum hrpos.le
      _ ≤ (eps/beta^2)*(M+1) := mul_le_mul_of_nonneg_right hrsmall (by positivity)
      _ = _ := by ring
  have h1 := (hjet1 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h2 := (hjet2 lam hlam δ hδ hδ1 R hR p hp x hx).1
  have h1k := (abs_coordinate_first_le k r x).trans h1
  have h1l := (abs_coordinate_first_le l r x).trans h1
  have h2kl := (abs_coordinate_second_le k l r hr x).trans h2
  have hm : TwoJetBound (coordinateDirection k) (coordinateDirection l)
      (fun _ : R3 => (1 : ℝ)) x M := by
    unfold TwoJetBound directionalFDeriv
    simp only [fderiv_const_apply,ContinuousLinearMap.zero_apply,abs_zero,abs_one]
    exact ⟨hM,by linarith,by linarith,by linarith⟩
  have ht := density_principal_first_second_bounds (coordinateDirection k) (coordinateDirection l)
    (fun _ : R3 => (1:ℝ)) r q (fun y => h y i j) contDiff_const hr hq (hh i j) x
    M J1 J2 beta eps hM hJ1.le hJ2.le hb heps heps1 hrpos hsmall hm hqq (hhjet i j k l)
    (by simpa only [pow_one] using h1k) (by simpa only [pow_one] using h1l) h2kl
  have he : densityPrincipalEntry (fun _ : R3 => (1 : ℝ)) r q (fun y => h y i j) =
      (fun y => actualPrincipalMatrix g L lam δ R p h y i j) := by
    funext y
    simp only [densityPrincipalEntry,principalEntry,one_mul,r,q,actualPrincipalMatrix]
  rw [he] at ht
  exact ⟨ha0,ht.1,ht.2⟩

/-- Symmetric coefficient p_ij of [S,a partial^2], with s^k=-sum_l c_l^k A_l. -/
def principalSecondFrameCoefficient (a : MatrixField) (c : Fin 3 → Fin 3 → R3 → ℝ)
    (i j l : Fin 3) (x : R3) : ℝ :=
  ∑ k, (-(c l k x * directionalFDeriv (coordinateDirection k) (fun y => a y i j) x) +
    a x k i * directionalFDeriv (coordinateDirection k) (c l j) x +
    a x k j * directionalFDeriv (coordinateDirection k) (c l i) x)

def principalSecondFrameCoefficientDerivative (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (i j l m : Fin 3) (x : R3) : ℝ :=
  ∑ k, (-(directionalFDeriv (coordinateDirection m) (c l k) x *
      directionalFDeriv (coordinateDirection k) (fun y => a y i j) x +
    c l k x * directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (fun y => a y i j)) x) +
    (directionalFDeriv (coordinateDirection m) (fun y => a y k i) x *
      directionalFDeriv (coordinateDirection k) (c l j) x +
      a x k i * directionalFDeriv (coordinateDirection m)
        (directionalFDeriv (coordinateDirection k) (c l j)) x) +
    (directionalFDeriv (coordinateDirection m) (fun y => a y k j) x *
      directionalFDeriv (coordinateDirection k) (c l i) x +
      a x k j * directionalFDeriv (coordinateDirection m)
        (directionalFDeriv (coordinateDirection k) (c l i)) x))

lemma directional_neg (X : R3) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    directionalFDeriv X (fun y => -f y) x = -directionalFDeriv X f x := by
  have h := directionalFDeriv_smul X (fun _ : R3 => (-1 : ℝ)) f contDiff_const hf x
  simpa [directionalFDeriv,smul_eq_mul] using h

lemma directional_principalSecondFrameCoefficient (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j))
    (hc : ∀ l k, ContDiff ℝ ∞ (c l k)) (i j l m : Fin 3) (x : R3) :
    directionalFDeriv (coordinateDirection m) (principalSecondFrameCoefficient a c i j l) x =
      principalSecondFrameCoefficientDerivative a c i j l m x := by
  have ht (k : Fin 3) : ContDiff ℝ ∞ (fun y =>
      -(c l k y * directionalFDeriv (coordinateDirection k) (fun z => a z i j) y) +
      a y k i * directionalFDeriv (coordinateDirection k) (c l j) y +
      a y k j * directionalFDeriv (coordinateDirection k) (c l i) y) :=
    (((hc l k).mul (contDiff_directionalFDeriv _ _ (ha i j))).neg.add
      ((ha k i).mul (contDiff_directionalFDeriv _ _ (hc l j)))).add
      ((ha k j).mul (contDiff_directionalFDeriv _ _ (hc l i)))
  unfold principalSecondFrameCoefficient principalSecondFrameCoefficientDerivative
  rw [directionalFDeriv_fintype_sum _ _ ht x]
  apply Finset.sum_congr rfl
  intro k hk
  rw [directionalFDeriv_add _ _ _
    (((hc l k).mul (contDiff_directionalFDeriv _ _ (ha i j))).neg.add
      ((ha k i).mul (contDiff_directionalFDeriv _ _ (hc l j))))
    ((ha k j).mul (contDiff_directionalFDeriv _ _ (hc l i))),
    directionalFDeriv_add _ _ _
      ((hc l k).mul (contDiff_directionalFDeriv _ _ (ha i j))).neg
      ((ha k i).mul (contDiff_directionalFDeriv _ _ (hc l j))),
    directional_neg _ _ ((hc l k).mul (contDiff_directionalFDeriv _ _ (ha i j))),
    directional_mul _ _ _ (hc l k) (contDiff_directionalFDeriv _ _ (ha i j)),
    directional_mul _ _ _ (ha k i) (contDiff_directionalFDeriv _ _ (hc l j)),
    directional_mul _ _ _ (ha k j) (contDiff_directionalFDeriv _ _ (hc l i))]

lemma abs_three_add_le (u v w : ℝ) : |u+v+w| ≤ |u|+|v|+|w| :=
  (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

lemma principalSecondFrameCoefficient_bound (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (x : R3) (A0 A1 F : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (ha0 : ∀ i j, |a x i j| ≤ A0)
    (ha1 : ∀ i j k, |directionalFDeriv (coordinateDirection k) (fun y => a y i j) x| ≤ A1)
    (hc0 : ∀ l k, |c l k x| ≤ F)
    (hc1 : ∀ l k m, |directionalFDeriv (coordinateDirection m) (c l k) x| ≤ F)
    (i j l : Fin 3) : |principalSecondFrameCoefficient a c i j l x| ≤ 3*F*(A1+2*A0) := by
  have hslot (k : Fin 3) :
      |-(c l k x * directionalFDeriv (coordinateDirection k) (fun y => a y i j) x) +
        a x k i * directionalFDeriv (coordinateDirection k) (c l j) x +
        a x k j * directionalFDeriv (coordinateDirection k) (c l i) x| ≤ F*(A1+2*A0) := by
    have h1 : |-(c l k x * directionalFDeriv (coordinateDirection k) (fun y => a y i j) x)| ≤ F*A1 := by
      rw [abs_neg,abs_mul]
      exact mul_le_mul (hc0 l k) (ha1 i j k) (abs_nonneg _) hF
    have h2 : |a x k i * directionalFDeriv (coordinateDirection k) (c l j) x| ≤ A0*F := by
      rw [abs_mul]
      exact mul_le_mul (ha0 k i) (hc1 l j k) (abs_nonneg _) hA0
    have h3 : |a x k j * directionalFDeriv (coordinateDirection k) (c l i) x| ≤ A0*F := by
      rw [abs_mul]
      exact mul_le_mul (ha0 k j) (hc1 l i k) (abs_nonneg _) hA0
    exact (abs_three_add_le _ _ _).trans (by nlinarith)
  have hs := abs_sum_three_le _ _ hslot
  simpa only [principalSecondFrameCoefficient,mul_assoc] using hs

lemma principalSecondFrameCoefficientDerivative_bound (a : MatrixField)
    (c : Fin 3 → Fin 3 → R3 → ℝ) (x : R3) (A0 A1 A2 F : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hF : 0 ≤ F)
    (ha0 : ∀ i j, |a x i j| ≤ A0)
    (ha1 : ∀ i j k, |directionalFDeriv (coordinateDirection k) (fun y => a y i j) x| ≤ A1)
    (ha2 : ∀ i j k m, |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (fun y => a y i j)) x| ≤ A2)
    (hc0 : ∀ l k, |c l k x| ≤ F)
    (hc1 : ∀ l k m, |directionalFDeriv (coordinateDirection m) (c l k) x| ≤ F)
    (hc2 : ∀ l k n m, |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection n) (c l k)) x| ≤ F)
    (i j l m : Fin 3) :
    |principalSecondFrameCoefficientDerivative a c i j l m x| ≤ 3*F*(A2+3*A1+2*A0) := by
  have hab (u v : ℝ) (A B : ℝ) (hA : 0 ≤ A) (hu : |u| ≤ A) (hv : |v| ≤ B) :
      |u*v| ≤ A*B := by rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) hA
  have hslot (k : Fin 3) :
      |-(directionalFDeriv (coordinateDirection m) (c l k) x *
          directionalFDeriv (coordinateDirection k) (fun y => a y i j) x +
        c l k x * directionalFDeriv (coordinateDirection m)
          (directionalFDeriv (coordinateDirection k) (fun y => a y i j)) x) +
      (directionalFDeriv (coordinateDirection m) (fun y => a y k i) x *
        directionalFDeriv (coordinateDirection k) (c l j) x +
        a x k i * directionalFDeriv (coordinateDirection m)
          (directionalFDeriv (coordinateDirection k) (c l j)) x) +
      (directionalFDeriv (coordinateDirection m) (fun y => a y k j) x *
        directionalFDeriv (coordinateDirection k) (c l i) x +
        a x k j * directionalFDeriv (coordinateDirection m)
          (directionalFDeriv (coordinateDirection k) (c l i)) x)| ≤
      (F*A1+F*A2)+(A1*F+A0*F)+(A1*F+A0*F) := by
    have h1 := hab _ _ F A1 hF (hc1 l k m) (ha1 i j k)
    have h2 := hab _ _ F A2 hF (hc0 l k) (ha2 i j k m)
    have h3 := hab _ _ A1 F hA1 (ha1 k i m) (hc1 l j k)
    have h4 := hab _ _ A0 F hA0 (ha0 k i) (hc2 l j k m)
    have h5 := hab _ _ A1 F hA1 (ha1 k j m) (hc1 l i k)
    have h6 := hab _ _ A0 F hA0 (ha0 k j) (hc2 l i k m)
    have h12 : |-(directionalFDeriv (coordinateDirection m) (c l k) x *
        directionalFDeriv (coordinateDirection k) (fun y => a y i j) x +
        c l k x * directionalFDeriv (coordinateDirection m)
          (directionalFDeriv (coordinateDirection k) (fun y => a y i j)) x)| ≤ F*A1+F*A2 := by
      rw [abs_neg]
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    exact (abs_three_add_le _ _ _).trans
      (add_le_add (add_le_add h12 ((abs_add_le _ _).trans (add_le_add h3 h4)))
        ((abs_add_le _ _).trans (add_le_add h5 h6)))
  have hs := abs_sum_three_le _
    ((F*A1+F*A2)+(A1*F+A0*F)+(A1*F+A0*F)) hslot
  calc
    _ ≤ 3*((F*A1+F*A2)+(A1*F+A0*F)+(A1*F+A0*F)) := hs
    _ = _ := by ring

/-- The exact actual source principal coefficient; no operator-order placeholder occurs. -/
def actualPrincipalSecondFrameCoefficient (g : MatrixField) (L lam δ R : ℝ) (p : ℕ)
    (h : MatrixField) (i j l : Fin 3) : R3 → ℝ :=
  principalSecondFrameCoefficient (actualPrincipalMatrix g L lam δ R p h)
    (fun l k x => referenceFrameEntryFamily g L l k (lam,x)) i j l

lemma div_le_self_of_one_le (t b : ℝ) (ht : 0 ≤ t) (hb : 1 ≤ b) : t/b ≤ t := by
  apply (div_le_iff₀ (by linarith : 0 < b)).mpr
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hb)]

/-- Derived original epsilon/beta and epsilon derivative classes for the actual principal p. -/
theorem exists_actual_principal_second_frame_uniform_bounds (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
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
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j l m,
        |actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x| ≤ P*eps/beta ∧
        |directionalFDeriv (coordinateDirection m)
          (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l) x| ≤ Pd*eps := by
  obtain ⟨C0,C1,C2,hC0,hC1,hC2,hajet⟩ :=
    exists_actual_principal_uniform_two_jet_bound g hg L hL K hK
  obtain ⟨F,hF,hcjet⟩ := exists_referenceFrame_uniform_two_jet_bound g hg L K hK
  refine ⟨3*F*(C1+2*C0),3*F*(C2+3*C1+2*C0),by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i j l m
  let a := actualPrincipalMatrix g L lam δ R p h
  let c : Fin 3 → Fin 3 → R3 → ℝ := fun l k y => referenceFrameEntryFamily g L l k (lam,y)
  have ha := hajet lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall
  have hc0 (l k : Fin 3) : |c l k x| ≤ F := hcjet lam hlam x hx l k (.inl ())
  have hc1 (l k n : Fin 3) : |directionalFDeriv (coordinateDirection n) (c l k) x| ≤ F :=
    hcjet lam hlam x hx l k (.inr (.inl n))
  have hc2 (l k n m : Fin 3) : |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection n) (c l k)) x| ≤ F :=
    hcjet lam hlam x hx l k (.inr (.inr (n,m)))
  have hbeta : 0 < beta := by linarith
  have ha0 (i j : Fin 3) : |a x i j| ≤ C0*eps/beta :=
    (ha i j 0 0).1.trans (div_le_div_of_nonneg_left (by positivity) hbeta (by nlinarith))
  have ha1 (i j k : Fin 3) : |directionalFDeriv (coordinateDirection k)
      (fun y => a y i j) x| ≤ C1*eps/beta := (ha i j k k).2.1
  have ha0' (i j : Fin 3) : |a x i j| ≤ C0*eps :=
    (ha0 i j).trans (div_le_self_of_one_le _ _ (by positivity) hb)
  have ha1' (i j k : Fin 3) : |directionalFDeriv (coordinateDirection k)
      (fun y => a y i j) x| ≤ C1*eps :=
    (ha1 i j k).trans (div_le_self_of_one_le _ _ (by positivity) hb)
  have ha2 (i j k m : Fin 3) : |directionalFDeriv (coordinateDirection m)
      (directionalFDeriv (coordinateDirection k) (fun y => a y i j)) x| ≤ C2*eps :=
    (ha i j k m).2.2
  constructor
  · have ht := principalSecondFrameCoefficient_bound a c x
      (C0*eps/beta) (C1*eps/beta) F (by positivity) (by positivity) (by linarith)
      ha0 ha1 hc0 hc1 i j l
    convert ht using 1 <;> first | rfl | ring
  · have has (i j : Fin 3) : ContDiff ℝ ∞ (fun y => a y i j) :=
      contDiff_actualPrincipalMatrix_entry g hg L lam δ R p h hδ hR hh i j
    have hcs (l k : Fin 3) : ContDiff ℝ ∞ (c l k) :=
      (contDiff_referenceFrameEntryFamily g hg L l k).comp (contDiff_const.prodMk contDiff_id)
    have ht := principalSecondFrameCoefficientDerivative_bound a c x
      (C0*eps) (C1*eps) (C2*eps) F (by positivity) (by positivity) (by positivity)
      (by linarith) ha0' ha1' ha2 hc0 hc1 hc2 i j l m
    change |directionalFDeriv (coordinateDirection m) (principalSecondFrameCoefficient a c i j l) x| ≤ _
    rw [directional_principalSecondFrameCoefficient a c has hcs i j l m x]
    convert ht using 1 <;> first | rfl | ring

end OAI.AnisotropicCalderon.ActualPrincipalErrorCoefficient
