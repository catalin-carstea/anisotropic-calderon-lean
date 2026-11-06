import Calderon.ActualCoordinateOrderedH8
import Calderon.ActualReferenceDDHigherGeometryJets
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualReferenceDDHigherHCoframeJets
open ActualCoordinateOrderedH8 CoordinateBootstrapJets ActualReferenceDDHigherGeometryJets
  ActualHorizontalNormBridge ActualPhysicalMixedNative ActualPhysicalMixedReferenceCancellation
  PrincipalCommutator PerturbedDensityAdjoint ReferenceDensityBounds ConformalDepth RadiusProfile MetricOperator

def HasCoordinateWordJetBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → E) (x : R3) (C beta : ℝ) (s : ℕ) : Prop :=
  ∀ w : List (Fin 3), w.length ≤ N →
    ‖coordinateFieldWordPartial w f x‖ ≤ C*beta^(s+w.length)

lemma coordinateFieldWordPartial_append {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w v : List (Fin 3)) (f : R3 → E) :
    coordinateFieldWordPartial (w++v) f =
      coordinateFieldWordPartial w (coordinateFieldWordPartial v f) := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial (w++v) f) =
      directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (coordinateFieldWordPartial v f))
    rw [ih]

lemma coordinateFieldWordPartial_coordinate_derivative_commute {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin 3) (w : List (Fin 3)) (f : R3 → E) (hf : ContDiff ℝ ∞ f) :
    coordinateFieldWordPartial w (directionalFDeriv (coordinateDirection k) f) =
      directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    change directionalFDeriv (coordinateDirection l)
        (coordinateFieldWordPartial w (directionalFDeriv (coordinateDirection k) f)) =
      directionalFDeriv (coordinateDirection k)
        (directionalFDeriv (coordinateDirection l) (coordinateFieldWordPartial w f))
    rw [ih]
    funext x
    exact directionalFDeriv_commute (coordinateDirection l) (coordinateDirection k)
      (coordinateFieldWordPartial w f) (contDiff_coordinateFieldWordPartial w f hf) x

lemma coordinateFieldWordPartial_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (f g : R3 → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    coordinateFieldWordPartial w (fun y => f y+g y) =
      fun y => coordinateFieldWordPartial w f y+coordinateFieldWordPartial w g y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => f y+g y)) =
      fun y => directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f) y+
        directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w g) y
    rw [ih]
    funext x
    exact directionalFDeriv_add (coordinateDirection k) _ _
      (contDiff_coordinateFieldWordPartial w f hf) (contDiff_coordinateFieldWordPartial w g hg) x

lemma coordinateFieldWordPartial_sum {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (F : ι → R3 → E) (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    coordinateFieldWordPartial w (fun y => ∑ i : ι, F i y) =
      fun y => ∑ i : ι, coordinateFieldWordPartial w (F i) y := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun y => ∑ i : ι, F i y)) =
      fun y => ∑ i : ι, directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w (F i)) y
    rw [ih]
    funext x
    unfold directionalFDeriv
    rw [fderiv_fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      (contDiff_coordinateFieldWordPartial w (F i) (hF i)).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.sum_apply]

lemma coordinateFieldWordPartial_const {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : List (Fin 3)) (c : E) :
    coordinateFieldWordPartial w (fun _ : R3 => c) =
      fun _ => if w=[] then c else 0 := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k)
        (coordinateFieldWordPartial w (fun _ : R3 => c)) =
      fun _ => if k::w=[] then c else 0
    rw [ih]
    funext x
    change fderiv ℝ (fun _ : R3 => if w=[] then c else 0) x (coordinateDirection k) = 0
    rw [fderiv_const_apply]
    rfl

lemma hasCoordinateWordJetBound_mono {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → E) (x : R3) (C D beta : ℝ) (s : ℕ)
    (h : HasCoordinateWordJetBound N f x C beta s) (hCD : C ≤ D) (hb : 0 ≤ beta) :
    HasCoordinateWordJetBound N f x D beta s := by
  intro w hw
  exact (h w hw).trans (mul_le_mul_of_nonneg_right hCD (pow_nonneg hb _))

lemma hasCoordinateWordJetBound_truncate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M N : ℕ) (f : R3 → E) (x : R3) (C beta : ℝ) (s : ℕ)
    (h : HasCoordinateWordJetBound N f x C beta s) (hMN : M ≤ N) :
    HasCoordinateWordJetBound M f x C beta s := by
  intro w hw
  exact h w (hw.trans hMN)

lemma hasCoordinateWordJetBound_coordinate_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : R3 → E) (x : R3) (C beta : ℝ) (s : ℕ) (k : Fin 3)
    (h : HasCoordinateWordJetBound (N+1) f x C beta s) :
    HasCoordinateWordJetBound N (directionalFDeriv (coordinateDirection k) f) x C beta (s+1) := by
  intro w hw
  have ht := h (w++[k]) (by simp only [List.length_append,List.length_singleton]; omega)
  simpa only [coordinateFieldWordPartial_append,coordinateFieldWordPartial,
    List.length_append,List.length_singleton,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

lemma hasCoordinateWordJetBound_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f g : R3 → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s : ℕ)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta s) :
    HasCoordinateWordJetBound N (fun y => f y+g y) x (C+D) beta s := by
  intro w hw
  rw [coordinateFieldWordPartial_add w f g hf hg]
  calc
    ‖coordinateFieldWordPartial w f x+coordinateFieldWordPartial w g x‖ ≤
        ‖coordinateFieldWordPartial w f x‖+‖coordinateFieldWordPartial w g x‖ := norm_add_le _ _
    _ ≤ C*beta^(s+w.length)+D*beta^(s+w.length) := add_le_add (hF w hw) (hG w hw)
    _ = (C+D)*beta^(s+w.length) := by ring

lemma hasCoordinateWordJetBound_mul
    (N : ℕ) (f g : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : R3) (C D beta : ℝ) (s t : ℕ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ beta)
    (hF : HasCoordinateWordJetBound N f x C beta s)
    (hG : HasCoordinateWordJetBound N g x D beta t) :
    HasCoordinateWordJetBound N (fun y => f y*g y) x ((2:ℝ)^N*C*D) beta (s+t) := by
  induction N generalizing f g C D s t with
  | zero =>
    intro w hw
    cases w with
    | nil =>
      change ‖f x*g x‖ ≤ ((2:ℝ)^0*C*D)*beta^(s+t)
      have hfx := hF [] (by simp)
      have hgx := hG [] (by simp)
      have hpow : 1 ≤ (2:ℝ)^0 := one_le_pow₀ (by norm_num)
      have hconst : C*D ≤ (2:ℝ)^0*C*D := by
        have ht := mul_le_mul_of_nonneg_right hpow (mul_nonneg hC hD)
        simpa only [one_mul,mul_assoc] using ht
      calc
        ‖f x*g x‖ = ‖f x‖*‖g x‖ := norm_mul _ _
        _ ≤ (C*beta^s)*(D*beta^t) := by
          exact mul_le_mul (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hfx)
            (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hgx)
            (norm_nonneg _) (mul_nonneg hC (pow_nonneg hb _))
        _ = C*D*beta^(s+t) := by rw [pow_add]; ring
        _ ≤ ((2:ℝ)^0*C*D)*beta^(s+t) :=
          mul_le_mul_of_nonneg_right hconst (pow_nonneg hb _)
    | cons k v => simp at hw
  | succ N ih =>
    intro w hw
    cases w with
    | nil =>
      change ‖f x*g x‖ ≤ ((2:ℝ)^(N+1)*C*D)*beta^(s+t)
      have hfx := hF [] (by simp)
      have hgx := hG [] (by simp)
      have hpow : 1 ≤ (2:ℝ)^(N+1) := one_le_pow₀ (by norm_num)
      have hconst : C*D ≤ (2:ℝ)^(N+1)*C*D := by
        have ht := mul_le_mul_of_nonneg_right hpow (mul_nonneg hC hD)
        simpa only [one_mul,mul_assoc] using ht
      calc
        ‖f x*g x‖ = ‖f x‖*‖g x‖ := norm_mul _ _
        _ ≤ (C*beta^s)*(D*beta^t) := by
          exact mul_le_mul (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hfx)
            (by simpa only [coordinateFieldWordPartial,List.length_nil,Nat.add_zero] using hgx)
            (norm_nonneg _) (mul_nonneg hC (pow_nonneg hb _))
        _ = C*D*beta^(s+t) := by rw [pow_add]; ring
        _ ≤ ((2:ℝ)^(N+1)*C*D)*beta^(s+t) :=
          mul_le_mul_of_nonneg_right hconst (pow_nonneg hb _)
    | cons k v =>
      have hv : v.length ≤ N := by simp only [List.length_cons] at hw; omega
      let fk : R3 → ℝ := directionalFDeriv (coordinateDirection k) f
      let gk : R3 → ℝ := directionalFDeriv (coordinateDirection k) g
      have hfk : ContDiff ℝ ∞ fk := contDiff_directionalFDeriv (coordinateDirection k) f hf
      have hgk : ContDiff ℝ ∞ gk := contDiff_directionalFDeriv (coordinateDirection k) g hg
      have hFk : HasCoordinateWordJetBound N fk x C beta (s+1) :=
        hasCoordinateWordJetBound_coordinate_derivative N f x C beta s k hF
      have hGk : HasCoordinateWordJetBound N gk x D beta (t+1) :=
        hasCoordinateWordJetBound_coordinate_derivative N g x D beta t k hG
      have hFt : HasCoordinateWordJetBound N f x C beta s :=
        hasCoordinateWordJetBound_truncate N (N+1) f x C beta s hF (by omega)
      have hGt : HasCoordinateWordJetBound N g x D beta t :=
        hasCoordinateWordJetBound_truncate N (N+1) g x D beta t hG (by omega)
      have h1 : HasCoordinateWordJetBound N (fun y => fk y*g y) x
          ((2:ℝ)^N*C*D) beta ((s+1)+t) :=
        ih (f := fk) (g := g) (hf := hfk) (hg := hg) (C := C) (D := D)
          (s := s+1) (t := t) (hC := hC) (hD := hD) (hF := hFk) (hG := hGt)
      have h2 : HasCoordinateWordJetBound N (fun y => f y*gk y) x
          ((2:ℝ)^N*C*D) beta (s+(t+1)) :=
        ih (f := f) (g := gk) (hf := hf) (hg := hgk) (C := C) (D := D)
          (s := s) (t := t+1) (hC := hC) (hD := hD) (hF := hFt) (hG := hGk)
      have he : directionalFDeriv (coordinateDirection k) (fun y => f y*g y) =
          fun y => fk y*g y+f y*gk y := by
        funext y
        exact directional_mul (coordinateDirection k) f g hf hg y
      change ‖directionalFDeriv (coordinateDirection k)
          (coordinateFieldWordPartial v (fun y => f y*g y)) x‖ ≤
        ((2:ℝ)^(N+1)*C*D)*beta^(s+t+(v.length+1))
      rw [← coordinateFieldWordPartial_coordinate_derivative_commute k v _ (hf.mul hg),he,
        coordinateFieldWordPartial_add v _ _ (hfk.mul hg) (hf.mul hgk)]
      have ht1 := h1 v hv
      have ht2 := h2 v hv
      have he1 : (s+1)+t+v.length=s+t+(v.length+1) := by omega
      have he2 : s+(t+1)+v.length=s+t+(v.length+1) := by omega
      rw [he1] at ht1
      rw [he2] at ht2
      calc
        ‖coordinateFieldWordPartial v (fun y => fk y*g y) x+
            coordinateFieldWordPartial v (fun y => f y*gk y) x‖ ≤
            ‖coordinateFieldWordPartial v (fun y => fk y*g y) x‖+
              ‖coordinateFieldWordPartial v (fun y => f y*gk y) x‖ := norm_add_le _ _
        _ ≤ ((2:ℝ)^N*C*D)*beta^(s+t+(v.length+1))+
              ((2:ℝ)^N*C*D)*beta^(s+t+(v.length+1)) := add_le_add ht1 ht2
        _ = ((2:ℝ)^(N+1)*C*D)*beta^(s+t+(v.length+1)) := by rw [pow_succ]; ring

lemma hasCoordinateWordJetBound_const (N : ℕ) (c : ℝ) (x : R3) (C beta : ℝ)
    (hC : |c| ≤ C) (hb : 1 ≤ beta) :
    HasCoordinateWordJetBound N (fun _ => c) x C beta 0 := by
  intro w hw
  rw [coordinateFieldWordPartial_const]
  by_cases hw0 : w=[]
  · subst w
    simpa using hC
  · have hC0 : 0 ≤ C := (abs_nonneg c).trans hC
    have hb0 : 0 ≤ beta := by linarith
    simp only [if_neg hw0,norm_zero]
    exact mul_nonneg hC0 (pow_nonneg hb0 _)

lemma hasCoordinateWordJetBound_sum {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (F : ι → R3 → E) (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (x : R3) (C beta : ℝ) (s : ℕ)
    (hB : ∀ i, HasCoordinateWordJetBound N (F i) x C beta s) :
    HasCoordinateWordJetBound N (fun y => ∑ i : ι, F i y) x
      ((Fintype.card ι : ℝ)*C) beta s := by
  intro w hw
  rw [coordinateFieldWordPartial_sum w F hF]
  calc
    ‖∑ i : ι, coordinateFieldWordPartial w (F i) x‖ ≤
        ∑ i : ι, ‖coordinateFieldWordPartial w (F i) x‖ := norm_sum_le (s := Finset.univ)
          (f := fun i : ι => coordinateFieldWordPartial w (F i) x)
    _ ≤ ∑ i : ι, C*beta^(s+w.length) := Finset.sum_le_sum (fun i _ => hB i w hw)
    _ = (Fintype.card ι : ℝ)*C*beta^(s+w.length) := by simp [mul_assoc]

lemma coordinateFieldWordPartial_eq_coordinateWordPartial
    (w : List (Fin 3)) (f : R3 → ℝ) :
    coordinateFieldWordPartial w f = coordinateWordPartial w f := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change directionalFDeriv (coordinateDirection k) (coordinateFieldWordPartial w f) =
      coordinateDerivative k (coordinateWordPartial w f)
    rw [ih]
    rfl

lemma hasCoordinateWordJetBound_component_of_H8
    (N : ℕ) (hN : N ≤ 8) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) (x : R3) (i j : Fin 3)
    (eps beta δ R L : ℝ) (p : ℕ) (heps : 0 ≤ eps) (hb : 1 ≤ beta)
    (hδ : 0 < δ) (hR : 0 < R) (hH8 : coordinateH8 h x ≤ eps*referenceRadius δ R p L x) :
    HasCoordinateWordJetBound N (fun y => h y i j) x
      (eps*referenceRadius δ R p L x) beta 0 := by
  intro w hw
  rw [coordinateFieldWordPartial_eq_coordinateWordPartial]
  simpa only [Real.norm_eq_abs,Nat.zero_add] using
    abs_coordinateWordPartial_component_weighted_of_H8 w (hw.trans hN) h hh x i j
      eps beta δ R L p heps hb hδ hR hH8

theorem exists_physicalMixedFrameCoefficient_uniform_coordinate_word_bounds
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) (hN : N ≤ 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ R : ℝ, 0 < δ → 0 < R → ∀ p : ℕ, ∀ eps beta : ℝ,
      0 ≤ eps → eps ≤ 1 → 1 ≤ beta → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) → ∀ x ∈ K,
      coordinateH8 h x ≤ eps*referenceRadius δ R p L x →
      referenceRadius δ R p L x*beta^2 ≤ eps →
      ∀ a b : Fin 3, ∀ w : List (Fin 3), w.length ≤ N →
      |coordinateFieldWordPartial w (physicalMixedFrameCoefficient g L lam h a b) x| ≤
        C*eps*referenceRadius δ R p L x*beta^w.length ∧
      |coordinateFieldWordPartial w (physicalMixedQFrameCoefficient g L lam h a b) x| ≤
        (1+C)*beta^w.length := by
  obtain ⟨M,hM,hgeom⟩ := exists_parameter_coordinate_word_uniform_bound
    (fun t : Fin 3 × Fin 3 => referenceCoFrameEntry g L t.1 t.2)
    (fun t => contDiff_referenceCoFrameEntry g hg L t.1 t.2) K hK N
  let C : ℝ := 9*((2:ℝ)^N)^2*M^2
  have hM0 : 0 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro lam hlam δ R hδ hR p eps beta heps heps1 hb h hh x hx hH8 hsmall a b w hw
  let r : ℝ := referenceRadius δ R p L x
  have hr : 0 < r := referenceRadius_pos δ R p L x hδ hR
  have hb0 : 0 ≤ beta := by linarith
  have hepsr0 : 0 ≤ eps*r := mul_nonneg heps hr.le
  have hthetaS (i a : Fin 3) : ContDiff ℝ ∞
      (fun y => referenceCoFrameEntry g L i a (lam,y)) :=
    (contDiff_referenceCoFrameEntry g hg L i a).comp (contDiff_const.prodMk contDiff_id)
  have htheta (i a : Fin 3) : HasCoordinateWordJetBound N
      (fun y => referenceCoFrameEntry g L i a (lam,y)) x M beta 0 := by
    intro v hv
    have ht := hgeom lam hlam x hx (i,a) v hv
    have hp : 1 ≤ beta^v.length := one_le_pow₀ hb
    have hm := mul_le_mul_of_nonneg_left hp hM0
    exact ht.trans (by simpa only [Nat.zero_add,mul_one] using hm)
  have hhB (i j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => h y i j) x (eps*r) beta 0 :=
    hasCoordinateWordJetBound_component_of_H8 N hN h hh x i j
      eps beta δ R L p heps hb hδ hR hH8
  let A : ℝ := (2:ℝ)^N*((2:ℝ)^N*(eps*r)*M)*M
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have htermS (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) :=
    ((hh i j).mul (hthetaS i a)).mul (hthetaS j b)
  have hterm (i j : Fin 3) : HasCoordinateWordJetBound N
      (fun y => h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) x A beta 0 := by
    have ht1 := hasCoordinateWordJetBound_mul N (fun y => h y i j)
      (fun y => referenceCoFrameEntry g L i a (lam,y)) (hh i j) (hthetaS i a)
      x (eps*r) M beta 0 0 hepsr0 hM0 hb0 (hhB i j) (htheta i a)
    have hc1 : 0 ≤ (2:ℝ)^N*(eps*r)*M := by positivity
    have ht2 := hasCoordinateWordJetBound_mul N
      (fun y => h y i j*referenceCoFrameEntry g L i a (lam,y))
      (fun y => referenceCoFrameEntry g L j b (lam,y)) ((hh i j).mul (hthetaS i a)) (hthetaS j b)
      x ((2:ℝ)^N*(eps*r)*M) M beta 0 0 hc1 hM0 hb0 ht1 (htheta j b)
    exact ht2
  have hsumS (i : Fin 3) : ContDiff ℝ ∞
      (fun y => ∑ j : Fin 3, h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) :=
    ContDiff.sum (fun j _ => htermS i j)
  have hsum (i : Fin 3) : HasCoordinateWordJetBound N
      (fun y => ∑ j : Fin 3, h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) x (3*A) beta 0 := by
    simpa only [Fintype.card_fin,Nat.cast_ofNat] using hasCoordinateWordJetBound_sum N
      (fun j : Fin 3 => fun y => h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) (htermS i) x A beta 0 (hterm i)
  have htotal := hasCoordinateWordJetBound_sum N
    (fun i : Fin 3 => fun y => ∑ j : Fin 3, h y i j*referenceCoFrameEntry g L i a (lam,y)*
      referenceCoFrameEntry g L j b (lam,y)) hsumS x (3*A) beta 0 hsum
  have htotal' : HasCoordinateWordJetBound N (physicalMixedFrameCoefficient g L lam h a b) x
      (3*(3*A)) beta 0 := by
    change HasCoordinateWordJetBound N
      (fun y => ∑ i : Fin 3, ∑ j : Fin 3, h y i j*referenceCoFrameEntry g L i a (lam,y)*
        referenceCoFrameEntry g L j b (lam,y)) x (3*(3*A)) beta 0
    simpa only [Fintype.card_fin,Nat.cast_ofNat] using htotal
  have heConst : (3:ℝ)*(3*A)=C*(eps*r) := by dsimp [C,A]; ring
  rw [heConst] at htotal'
  have hr1 : r ≤ 1 := by
    have hb2 : 1 ≤ beta^2 := by nlinarith
    change r*beta^2 ≤ eps at hsmall
    nlinarith
  have hepsr1 : eps*r ≤ 1 := by
    have ht := mul_le_mul heps1 hr1 hr.le (by norm_num : (0:ℝ)≤1)
    simpa only [one_mul] using ht
  have hscale : C*(eps*r) ≤ C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hepsr1 hC.le
  have htotalC := hasCoordinateWordJetBound_mono N
    (physicalMixedFrameCoefficient g L lam h a b) x (C*(eps*r)) C beta 0 htotal' hscale hb0
  have hd : |if a=b then (1:ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  have hdelta := hasCoordinateWordJetBound_const N (if a=b then (1:ℝ) else 0) x 1 beta hd hb
  have hQ : HasCoordinateWordJetBound N (physicalMixedQFrameCoefficient g L lam h a b) x
      (1+C) beta 0 := by
    have he : physicalMixedQFrameCoefficient g L lam h a b =
        fun y => (if a=b then (1:ℝ) else 0)+physicalMixedFrameCoefficient g L lam h a b y :=
      funext (physicalMixedQFrameCoefficient_decomposition g hg L lam h a b)
    rw [he]
    exact hasCoordinateWordJetBound_add N (fun _ => if a=b then (1:ℝ) else 0)
      (physicalMixedFrameCoefficient g L lam h a b) contDiff_const
      (contDiff_physicalMixedFrameCoefficient g hg L lam h hh a b)
      x 1 C beta 0 hdelta htotalC
  refine ⟨?_,?_⟩
  · have ht := htotal' w hw
    simpa only [Real.norm_eq_abs,Nat.zero_add,mul_assoc] using ht
  · simpa only [Real.norm_eq_abs,Nat.zero_add] using hQ w hw

end OAI.AnisotropicCalderon.ActualReferenceDDHigherHCoframeJets
