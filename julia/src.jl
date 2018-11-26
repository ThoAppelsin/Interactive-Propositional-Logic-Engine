abstract type Formula end

struct Atom <: Formula
	p::String
end

struct Neg <: Formula
	ϕ::Formula
end

struct And <: Formula
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Or <: Formula
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Imp <: Formula
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Sequent
	Φ::Array{Formula}
	ψ::Formula
end

¬ϕ = Neg(ϕ)
ϕ ∧ ψ = And(ϕ, ψ)
ϕ ∨ ψ = Or(ϕ, ψ)
ϕ → ψ = Imp(ϕ, ψ)

@enum Assoc LeftAssoc RightAssoc

PARENS = ["()", "[]"]
ATOM = r"^[A-Za-z][0-9]*$"
NEG = ["!"]
AND = ["&", "*"]
OR  = ["|", "+"]
IMP = ["->"]
SEQ = ["=>"]

function balanced_parens(ϕ, parens)
	c = 0
	for x ∈ ϕ
		if x == parens[1]
			c += 1
		elseif x == parens[2]
			c -= 1
			if c < 0
				return false
			end
		end
	end
	return c == 0
end

balanced_parens(ϕ) = all(balanced_parens(ϕ, parens) for parens ∈ PARENS)

function parse_unary(ϕ, Op, OP)
	for op ∈ OP
		if startswith(ϕ, op)
			return Op(parse_formula(a[length(op)+1:end]))
		end
	end
end

function parse_binary(ϕ, Op, OP, assoc)
	for op ∈ OP
		splits = split(ϕ, op)
		e_range = (assoc == LeftAssoc ? reverse : identity)(1:length(splits)-1)
		for e ∈ e_range
			ϕ₁ = join(splits[1:e], op)
			ϕ₂ = join(splits[e+1:end], op)
			if balanced_parens(ϕ₁) && balanced_parens(ϕ₂)
				return Op(parse_formula(ϕ₁), parse_formula(ϕ₂))
			end
		end
	end
end

is_atomic(ϕ) = match(ATOM, ϕ) ≠ nothing
parse_neg(ϕ) = parse_unary(ϕ, Neg, NEG)
parse_and(ϕ) = parse_binary(ϕ, And, AND, LeftAssoc)
parse_or(ϕ)  = parse_binary(ϕ, Or, OR, LeftAssoc)
parse_imp(ϕ) = parse_binary(ϕ, Imp, IMP, RightAssoc)

function converge(subject, functions)
	while true
		subject_old = subject
		for f ∈ functions
			subject = f(subject)
		end
		if subject_old == subject
			return subject
		end
	end
end

strip_parens(ϕ, parens) = !isempty(ϕ) && ϕ[[1, end]] == parens ? ϕ[2:end-1] : ϕ
strip_parens(ϕ) = converge(ϕ, [ϕ -> strip_parens(ϕ, parens) for parens ∈ PARENS])
strip_formula(ϕ) = converge(ϕ, [strip, strip_parens])

function continue_abort()
	while true
		print("[C]ontinue/[A]bort? ")
		inp = chomp(readline())
		if inp == "c" || inp == "C"
			break
		elseif inp == "a" || inp == "A"
			println("Aborting")
			exit()
		end
	end
end

function parse_formula(ϕ)
	ϕ = strip_formula(ϕ)
	for p in [parse_imp, parse_or, parse_and, parse_neg]
		if (ϕ⁺ = p(ϕ)) ≠ nothing
			return ϕ⁺
		end
	end
	if !is_atomic(ϕ)
		println("Following will be regarded as an atomic proposition: >$ϕ<")
		continue_abort()
	end
	return Atom(ϕ)
end

function parse_sequent(Δ)
	Φ = ""
	ψ = Δ
	for seq ∈ SEQ
		splits = split(Δ, seq)
		if length(splits) == 2
			Φ, ψ = splits
			break
		end
		if length(splits) > 2
			println("Multiple $seq symbols detected")
			continue_abort()
		end
	end
	Φ = map(parse_formula, split(Φ, ',', keepempty=false))
	ψ = parse_formula(ψ)
	Sequent(Φ, ψ)
end

struct ProofStep
	ϕ::Formula
	rationale::String
end

Andᵢ(Γ, i, j) = if i ≤ length(Γ) && j ≤ length(Γ)
	[Γ; ProofStep(Γ[i].ϕ ∧ Γ[j].ϕ, "∧ᵢ $i, $j")]
end

Andₑ₁(Γ, i) = if i ≤ length(Γ)
	ϕ = Γ[i].ϕ
	if typeof(ϕ) == And
		[Γ; ProofStep(ϕ.ϕ₁, "∧ₑ₁ $i")]
	end
end

Andₑ₂(Γ, i) = if i ≤ length(Γ)
	ϕ = Γ[i].ϕ
	if typeof(ϕ) == And
		[Γ; ProofStep(ϕ.ϕ₂, "∧ₑ₂ $i")]
	end
end

Orᵢ₁(Γ, i, ψ) = if i ≤ length(Γ)
	ψ = parse_formula(ψ)
	[Γ; ProofStep(Γ[i].ϕ ∨ ψ, "∨ᵢ₁ $i")]
end

Orᵢ₂(Γ, i, ψ) = if i ≤ length(Γ)
	ψ = parse_formula(ψ)
	[Γ; ProofStep(ψ ∨ Γ[i].ϕ, "∨ᵢ₂ $i")]
end

Orₑ(Γ, i, j, k) = if 

# println(parse_sequent(length(ARGS) ≥ 1 ? ARGS[1] : "a & b"))
