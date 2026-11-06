import Calderon.ProfileFrechetJets
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Gradient Topology
namespace OAI.AnisotropicCalderon.RadiusProfile

abbrev CoordinateConnectionFamily := ℝ × R3 → R3 →L[ℝ] R3 →L[ℝ] R3

def jetBasisVector (i : Fin 3) : R3 := EuclideanSpace.single i 1

lemma norm_jetBasisVector (i : Fin 3) : ‖jetBasisVector i‖ = 1 := by
  simp [jetBasisVector, PiLp.norm_single]

def coordinatePartialJet (f : R3 → ℝ) (n : ℕ) (I : Fin n → Fin 3) (x : R3) : ℝ :=
  iteratedFDeriv ℝ n f x (fun i => jetBasisVector (I i))

lemma contDiff_coordinatePartialJet (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → Fin 3) : ContDiff ℝ ∞ (coordinatePartialJet f n I) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => R3) ℝ
    (fun i => jetBasisVector (I i))).contDiff.comp (hf.iteratedFDeriv_right (by simp))

lemma abs_coordinatePartialJet_le (f : R3 → ℝ) (n : ℕ) (I : Fin n → Fin 3) (x : R3) :
    |coordinatePartialJet f n I x| ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have h := (iteratedFDeriv ℝ n f x).le_opNorm (fun i => jetBasisVector (I i))
  simpa only [coordinatePartialJet, Real.norm_eq_abs, norm_jetBasisVector,
    Finset.prod_const_one, mul_one] using h

lemma fderiv_coordinatePartialJet_apply (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → Fin 3) (i : Fin 3) (x : R3) :
    fderiv ℝ (coordinatePartialJet f n I) x (jetBasisVector i) =
      coordinatePartialJet f (n + 1) (Fin.cons i I) x := by
  have hDn : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (by simp)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := hDn.differentiable (by simp) x
  let J : Fin (n + 1) → Fin 3 := Fin.cons i I
  have h := DifferentiableAt.iteratedFDeriv_succ_apply_left' (n := n) (f := f)
    (m := fun j : Fin (n + 1) => jetBasisVector (J j)) hd
  change fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (fun k => jetBasisVector (I k))) x
    (jetBasisVector i) = _
  simpa only [coordinatePartialJet, J, Fin.cons_zero, Fin.tail_cons, Fin.tail_def,
    Fin.cons_succ] using h.symm

def baseCoefficientDerivative (a : ℝ × R3 → ℝ) (i : Fin 3) (z : ℝ × R3) : ℝ :=
  fderiv ℝ (fun y => a (z.1, y)) z.2 (jetBasisVector i)

lemma baseCoefficientDerivative_eq_total (a : ℝ × R3 → ℝ)
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) (z : ℝ × R3) :
    baseCoefficientDerivative a i z = fderiv ℝ a z (0, jetBasisVector i) := by
  have hp : HasFDerivAt (fun y : R3 => (z.1, y)) (ContinuousLinearMap.inr ℝ ℝ R3) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have h := ((ha.differentiable (by simp) z).hasFDerivAt).comp z.2 hp
  change fderiv ℝ (a ∘ fun y : R3 => (z.1, y)) z.2 (jetBasisVector i) = _
  rw [h.fderiv]
  rfl

lemma contDiff_baseCoefficientDerivative (a : ℝ × R3 → ℝ)
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (baseCoefficientDerivative a i) := by
  have he : baseCoefficientDerivative a i = fun z => fderiv ℝ a z (0, jetBasisVector i) :=
    funext (baseCoefficientDerivative_eq_total a ha i)
  rw [he]
  exact (contDiff_infty_iff_fderiv.mp ha).2.clm_apply contDiff_const

/-- Actual coordinate covariant derivatives, with one correction per covector slot. -/
def covariantCoordinateJet (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) : (n : ℕ) → R3 → (Fin n → Fin 3) → ℝ
  | 0, x, _ => f x
  | n + 1, x, I =>
      fderiv ℝ (fun y => covariantCoordinateJet Γ f lam n y (Fin.tail I)) x
        (jetBasisVector (I 0)) -
      ∑ l : Fin n, ∑ k : Fin 3,
        (Γ (lam, x) (jetBasisVector (I 0)) (jetBasisVector ((Fin.tail I) l))) k *
          covariantCoordinateJet Γ f lam n x (Function.update (Fin.tail I) l k)

lemma covariantCoordinateJet_one (Γ : CoordinateConnectionFamily) (f : R3 → ℝ)
    (lam : ℝ) (x : R3) (I : Fin 1 → Fin 3) :
    covariantCoordinateJet Γ f lam 1 x I = fderiv ℝ f x (jetBasisVector (I 0)) := by
  simp [covariantCoordinateJet]

lemma covector_jetBasisVector_sum (F : R3 →L[ℝ] ℝ) (V : R3) :
    F V = ∑ k : Fin 3, V k * F (jetBasisVector k) := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr V
  calc
    F V = F (∑ k, ((EuclideanSpace.basisFun (Fin 3) ℝ).repr V) k •
      (EuclideanSpace.basisFun (Fin 3) ℝ) k) := congrArg F h.symm
    _ = _ := by simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, smul_eq_mul,
      EuclideanSpace.basisFun_apply, jetBasisVector]

lemma covariantCoordinateJet_two_eq_coordinateHessian
    (Γ : CoordinateConnectionFamily) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (x : R3) (i j : Fin 3) :
    covariantCoordinateJet Γ f lam 2 x (Fin.cons i (Fin.cons j Fin.elim0)) =
      coordinateHessian f (fun V W => Γ (lam, x) V W) x
        (jetBasisVector i) (jetBasisVector j) := by
  have hD := (contDiff_infty_iff_fderiv.mp hf).2
  have hd : fderiv ℝ (fun y => fderiv ℝ f y (jetBasisVector j)) x (jetBasisVector i) =
      fderiv ℝ (fderiv ℝ f) x (jetBasisVector i) (jetBasisVector j) := by
    rw [fderiv_clm_apply (hD.differentiable (by simp) x) (differentiableAt_const _)]
    simp
  rw [covariantCoordinateJet]
  simp only [covariantCoordinateJet_one, Fin.tail_cons, Fin.cons_zero, Fin.sum_univ_one,
    Function.update_self]
  change fderiv ℝ (fun y => fderiv ℝ f y (jetBasisVector j)) x (jetBasisVector i) -
    (∑ k : Fin 3, (Γ (lam, x) (jetBasisVector i) (jetBasisVector j)) k *
      fderiv ℝ f x (jetBasisVector k)) = _
  rw [hd, ← covector_jetBasisVector_sum]
  rfl

structure CoordinateJetTerm where
  coeff : ℝ × R3 → ℝ
  order : ℕ
  indices : Fin order → Fin 3

def coordinateTermValue (t : CoordinateJetTerm) (f : R3 → ℝ) (z : ℝ × R3) : ℝ :=
  t.coeff z * coordinatePartialJet f t.order t.indices z.2

def coordinateTermDerivative (i : Fin 3) (t : CoordinateJetTerm) : List CoordinateJetTerm :=
  [⟨baseCoefficientDerivative t.coeff i, t.order, t.indices⟩,
   ⟨t.coeff, t.order + 1, Fin.cons i t.indices⟩]

def coordinateTermMultiply (a : ℝ × R3 → ℝ) (t : CoordinateJetTerm) : CoordinateJetTerm :=
  ⟨fun z => a z * t.coeff z, t.order, t.indices⟩

def connectionCoordinateCoeff (Γ : CoordinateConnectionFamily) (i j k : Fin 3)
    (z : ℝ × R3) : ℝ := (Γ z (jetBasisVector i) (jetBasisVector j)) k

lemma contDiff_connectionCoordinateCoeff (Γ : CoordinateConnectionFamily)
    (hΓ : ContDiff ℝ ∞ Γ) (i j k : Fin 3) :
    ContDiff ℝ ∞ (connectionCoordinateCoeff Γ i j k) := by
  exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) k).contDiff.comp
    ((hΓ.clm_apply contDiff_const).clm_apply contDiff_const)

def covariantCoordinateExpansion (Γ : CoordinateConnectionFamily) :
    (n : ℕ) → (Fin n → Fin 3) → List CoordinateJetTerm
  | 0, _ => [⟨fun _ => 1, 0, Fin.elim0⟩]
  | n + 1, I =>
      (covariantCoordinateExpansion Γ n (Fin.tail I)).flatMap
        (coordinateTermDerivative (I 0)) ++
      (List.ofFn (fun l : Fin n => l)).flatMap (fun l =>
        (List.ofFn (fun k : Fin 3 => k)).flatMap (fun k =>
          (covariantCoordinateExpansion Γ n (Function.update (Fin.tail I) l k)).map
            (coordinateTermMultiply (fun z => -connectionCoordinateCoeff Γ (I 0) ((Fin.tail I) l) k z))))

lemma covariantCoordinateExpansion_coeff_smooth (Γ : CoordinateConnectionFamily)
    (hΓ : ContDiff ℝ ∞ Γ) (n : ℕ) (I : Fin n → Fin 3) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, ContDiff ℝ ∞ t.coeff := by
  induction n with
  | zero =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact contDiff_const
  | succ n ih =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact contDiff_baseCoefficientDerivative _ (ih (Fin.tail I) s hs) _
      · exact ih (Fin.tail I) s hs
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact (contDiff_connectionCoordinateCoeff Γ hΓ _ _ _).neg.mul
        (ih (Function.update (Fin.tail I) l k) s hs)

lemma covariantCoordinateExpansion_order_le (Γ : CoordinateConnectionFamily)
    (n : ℕ) (I : Fin n → Fin 3) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, t.order ≤ n := by
  induction n with
  | zero =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact le_rfl
  | succ n ih =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      have h := ih (Fin.tail I) s hs
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> dsimp only <;> omega
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih (Function.update (Fin.tail I) l k) s hs
      dsimp only [coordinateTermMultiply]
      omega

lemma baseCoefficientDerivative_const (c : ℝ) (i : Fin 3) :
    baseCoefficientDerivative (fun _ => c) i = 0 := by
  funext z
  simp [baseCoefficientDerivative]

lemma covariantCoordinateExpansion_zero_order_coeff (Γ : CoordinateConnectionFamily)
    (n : ℕ) (I : Fin n → Fin 3) (hn : 1 ≤ n) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, t.order = 0 → t.coeff = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro t ht hz
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · dsimp only at hz ⊢
        by_cases hzero : n = 0
        · subst n
          simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact baseCoefficientDerivative_const 1 _
        · rw [ih (Fin.tail I) (by omega) s hs hz]
          exact baseCoefficientDerivative_const 0 _
      · dsimp only at hz
        omega
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have hpos : 1 ≤ n := by have h := l.isLt; omega
      have hc := ih (Function.update (Fin.tail I) l k) hpos s hs hz
      funext z
      simp only [coordinateTermMultiply, hc, Pi.zero_apply, mul_zero]

def coordinateTermsValue (ts : List CoordinateJetTerm) (f : R3 → ℝ) (z : ℝ × R3) : ℝ :=
  (ts.map (fun t => coordinateTermValue t f z)).sum

lemma coordinateTermsValue_append (as bs : List CoordinateJetTerm) (f : R3 → ℝ)
    (z : ℝ × R3) : coordinateTermsValue (as ++ bs) f z =
      coordinateTermsValue as f z + coordinateTermsValue bs f z := by
  simp [coordinateTermsValue]

lemma coordinateTermsValue_flatMap {ι : Type*} (xs : List ι)
    (F : ι → List CoordinateJetTerm) (f : R3 → ℝ) (z : ℝ × R3) :
    coordinateTermsValue (xs.flatMap F) f z =
      (xs.map (fun i => coordinateTermsValue (F i) f z)).sum := by
  induction xs with
  | nil => simp [coordinateTermsValue]
  | cons x xs ih => simp [List.flatMap_cons, coordinateTermsValue_append, ih]

lemma coordinateTermsValue_multiply (a : ℝ × R3 → ℝ) (ts : List CoordinateJetTerm)
    (f : R3 → ℝ) (z : ℝ × R3) :
    coordinateTermsValue (ts.map (coordinateTermMultiply a)) f z =
      a z * coordinateTermsValue ts f z := by
  simp only [coordinateTermsValue, List.map_map, Function.comp_def,
    coordinateTermValue, coordinateTermMultiply, mul_assoc, List.sum_map_mul_left]

lemma contDiff_coordinateTermsValue_slice (ts : List CoordinateJetTerm)
    (hcoeff : ∀ t ∈ ts, ContDiff ℝ ∞ t.coeff)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (lam : ℝ) :
    ContDiff ℝ ∞ (fun x => coordinateTermsValue ts f (lam, x)) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih =>
    have ht : ContDiff ℝ ∞ (fun x : R3 => coordinateTermValue t f (lam, x)) :=
      ((hcoeff t (by simp)).comp (contDiff_const.prodMk contDiff_id)).mul
      (contDiff_coordinatePartialJet f hf t.order t.indices)
    have hts := ih (fun s hs => hcoeff s (by simp [hs]))
    exact ht.add hts

lemma fderiv_coordinateTermValue_slice_apply (t : CoordinateJetTerm)
    (ht : ContDiff ℝ ∞ t.coeff) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (x : R3) (i : Fin 3) :
    fderiv ℝ (fun y => coordinateTermValue t f (lam, y)) x (jetBasisVector i) =
      coordinateTermsValue (coordinateTermDerivative i t) f (lam, x) := by
  have ha : ContDiff ℝ ∞ (fun y : R3 => t.coeff (lam, y)) :=
    ht.comp (contDiff_const.prodMk contDiff_id)
  have hJ := contDiff_coordinatePartialJet f hf t.order t.indices
  unfold coordinateTermValue
  rw [fderiv_fun_mul (c := fun y => t.coeff (lam, y))
    (d := coordinatePartialJet f t.order t.indices)
    (ha.differentiable (by simp) x) (hJ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_coordinatePartialJet_apply f hf]
  simp only [coordinateTermsValue, coordinateTermDerivative, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, coordinateTermValue, baseCoefficientDerivative, add_zero]
  ring

lemma fderiv_coordinateTermsValue_slice_apply (ts : List CoordinateJetTerm)
    (hcoeff : ∀ t ∈ ts, ContDiff ℝ ∞ t.coeff)
    (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (lam : ℝ) (x : R3) (i : Fin 3) :
    fderiv ℝ (fun y => coordinateTermsValue ts f (lam, y)) x (jetBasisVector i) =
      coordinateTermsValue (ts.flatMap (coordinateTermDerivative i)) f (lam, x) := by
  induction ts with
  | nil => simp [coordinateTermsValue]
  | cons t ts ih =>
    have ht : ContDiff ℝ ∞ (fun y => coordinateTermValue t f (lam, y)) :=
      ((hcoeff t (by simp)).comp (contDiff_const.prodMk contDiff_id)).mul
        (contDiff_coordinatePartialJet f hf t.order t.indices)
    have hrest := contDiff_coordinateTermsValue_slice ts
      (fun s hs => hcoeff s (by simp [hs])) f hf lam
    have he : (fun y => coordinateTermsValue (t :: ts) f (lam, y)) =
        fun y => coordinateTermValue t f (lam, y) + coordinateTermsValue ts f (lam, y) := by
      funext y
      simp only [coordinateTermsValue, List.map_cons, List.sum_cons]
    rw [he, fderiv_fun_add (ht.differentiable (by simp) x) (hrest.differentiable (by simp) x)]
    simp only [add_apply, List.flatMap_cons, coordinateTermsValue_append]
    rw [fderiv_coordinateTermValue_slice_apply t (hcoeff t (by simp)) f hf,
      ih (fun s hs => hcoeff s (by simp [hs]))]

theorem covariantCoordinateJet_eq_expansion (Γ : CoordinateConnectionFamily)
    (hΓ : ContDiff ℝ ∞ Γ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (n : ℕ) (I : Fin n → Fin 3) (x : R3) :
    covariantCoordinateJet Γ f lam n x I =
      coordinateTermsValue (covariantCoordinateExpansion Γ n I) f (lam, x) := by
  induction n generalizing x with
  | zero => simp [covariantCoordinateJet, covariantCoordinateExpansion,
      coordinateTermsValue, coordinateTermValue, coordinatePartialJet]
  | succ n ih =>
    have he : (fun y => covariantCoordinateJet Γ f lam n y (Fin.tail I)) =
        fun y => coordinateTermsValue (covariantCoordinateExpansion Γ n (Fin.tail I)) f (lam, y) :=
      funext (fun y => ih (Fin.tail I) y)
    rw [covariantCoordinateJet, he,
      fderiv_coordinateTermsValue_slice_apply _
        (covariantCoordinateExpansion_coeff_smooth Γ hΓ _ _) f hf]
    rw [covariantCoordinateExpansion]
    rw [coordinateTermsValue_append, coordinateTermsValue_flatMap]
    simp only [coordinateTermsValue_flatMap, List.map_ofFn, Function.comp_def, List.sum_ofFn,
      coordinateTermsValue_multiply, ih, connectionCoordinateCoeff, neg_mul, Finset.sum_neg_distrib]
    ring

def covariantExpansionCoeffSum (Γ : CoordinateConnectionFamily) (n : ℕ)
    (I : Fin n → Fin 3) (z : ℝ × R3) : ℝ :=
  ((covariantCoordinateExpansion Γ n I).map (fun t => |t.coeff z|)).sum

lemma covariantExpansionCoeffSum_nonneg (Γ : CoordinateConnectionFamily)
    (n : ℕ) (I : Fin n → Fin 3) (z : ℝ × R3) :
    0 ≤ covariantExpansionCoeffSum Γ n I z := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  exact abs_nonneg _

lemma continuous_covariantExpansionCoeffSum (Γ : CoordinateConnectionFamily)
    (hΓ : ContDiff ℝ ∞ Γ) (n : ℕ) (I : Fin n → Fin 3) :
    Continuous (covariantExpansionCoeffSum Γ n I) := by
  have hs := covariantCoordinateExpansion_coeff_smooth Γ hΓ n I
  have hgen : ∀ ts : List CoordinateJetTerm,
      (∀ t ∈ ts, ContDiff ℝ ∞ t.coeff) →
      Continuous (fun z => (ts.map (fun t => |t.coeff z|)).sum) := by
    intro ts
    induction ts with
    | nil => intro _; exact continuous_const
    | cons t ts ih =>
      intro ht
      exact (ht t (by simp)).continuous.abs.add (ih (fun s hs => ht s (by simp [hs])))
  exact hgen _ hs

lemma abs_coordinateTermsValue_le_of_jets (ts : List CoordinateJetTerm)
    (horder : ∀ t ∈ ts, t.order ≤ n)
    (hzero : ∀ t ∈ ts, t.order = 0 → t.coeff = 0)
    (f : R3 → ℝ) (z : ℝ × R3) (beta B J : ℝ)
    (hbeta : 0 ≤ beta) (hB : 1 ≤ B) (hBa : 1 ≤ B * beta) (hJ : 0 ≤ J)
    (hjets : ∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f z.2‖ ≤ J * beta ^ k) :
    |coordinateTermsValue ts f z| ≤
      (ts.map (fun t => |t.coeff z|)).sum * J * (B * beta) ^ n := by
  have hterm : ∀ t ∈ ts, |coordinateTermValue t f z| ≤
      |t.coeff z| * J * (B * beta) ^ n := by
    intro t ht
    by_cases hz : t.order = 0
    · simp [coordinateTermValue, hzero t ht hz]
    · have hp : beta ^ t.order ≤ (B * beta) ^ n := by
        have hmul : beta ≤ B * beta := by nlinarith
        exact (pow_le_pow_left₀ hbeta hmul _).trans (pow_le_pow_right₀ hBa (horder t ht))
      have h := (abs_coordinatePartialJet_le f t.order t.indices z.2).trans
        ((hjets t.order (by omega) (horder t ht)).trans
          (mul_le_mul_of_nonneg_left hp hJ))
      have hm := mul_le_mul_of_nonneg_left h (abs_nonneg (t.coeff z))
      simpa only [coordinateTermValue, abs_mul, mul_assoc] using hm
  have hgen : ∀ us : List CoordinateJetTerm,
      (∀ t ∈ us, |coordinateTermValue t f z| ≤ |t.coeff z| * J * (B * beta) ^ n) →
      |coordinateTermsValue us f z| ≤
        (us.map (fun t => |t.coeff z|)).sum * J * (B * beta) ^ n := by
    intro us
    induction us with
    | nil => intro _; simp [coordinateTermsValue]
    | cons t us ih =>
      intro ht
      have hfirst := ht t (by simp)
      have hrest := ih (fun s hs => ht s (by simp [hs]))
      simp only [coordinateTermsValue, List.map_cons, List.sum_cons] at hrest ⊢
      exact (abs_add_le _ _).trans (by nlinarith)
  exact hgen _ hterm

theorem exists_covariantCoordinateJet_compact_bound (Γ : CoordinateConnectionFamily)
    (hΓ : ContDiff ℝ ∞ Γ) (n : ℕ) (hn : 1 ≤ n) (K : Set R3) (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ I : Fin n → Fin 3, ∀ f : R3 → ℝ, ContDiff ℝ ∞ f →
      ∀ beta B J : ℝ, 0 ≤ beta → 1 ≤ B → 1 ≤ B * beta → 0 ≤ J →
      (∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ J * beta ^ k) →
      |covariantCoordinateJet Γ f lam n x I| ≤ A * J * B ^ n * beta ^ n := by
  let S : ℝ × R3 → ℝ := fun z => ∑ I : Fin n → Fin 3, covariantExpansionCoeffSum Γ n I z
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro I _
    exact continuous_covariantExpansionCoeffSum Γ hΓ n I
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro lam hlam x hx I f hf beta B J hbeta hB hBa hJ hjets
  rw [covariantCoordinateJet_eq_expansion Γ hΓ f hf]
  have h := abs_coordinateTermsValue_le_of_jets _
    (covariantCoordinateExpansion_order_le Γ n I)
    (covariantCoordinateExpansion_zero_order_coeff Γ n I hn)
    f (lam, x) beta B J hbeta hB hBa hJ hjets
  have hcoeff : covariantExpansionCoeffSum Γ n I (lam, x) ≤ max C 0 := by
    have hsingle : covariantExpansionCoeffSum Γ n I (lam, x) ≤ S (lam, x) := by
      exact Finset.single_le_sum (s := Finset.univ) (a := I)
        (f := fun J => covariantExpansionCoeffSum Γ n J (lam, x))
        (fun J _ => covariantExpansionCoeffSum_nonneg Γ n J _) (Finset.mem_univ I)
    exact hsingle.trans (((le_abs_self _).trans (hC (lam, x) ⟨hlam, hx⟩)).trans (le_max_left _ _))
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ J * (B * beta) ^ n from
      mul_nonneg hJ (pow_nonneg (mul_nonneg (show 0 ≤ B by linarith) hbeta) n))
  have he : (max C 0) * (J * (B * beta) ^ n) = max C 0 * J * B ^ n * beta ^ n := by
    rw [mul_pow]
    ring
  rw [he] at hm
  exact h.trans (by simpa only [covariantExpansionCoeffSum, mul_assoc] using hm)

end OAI.AnisotropicCalderon.RadiusProfile
