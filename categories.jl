using Metatheory
using Metatheory.EGraphs
using Metatheory.Library

struct Category
    src::Dict
    target::Dict
    relations
end

# Initialize a category and test it 
function categoryInit(src::Dict, target::Dict, relations)

    identity = @theory f begin
        1 ∘ f == f 
        f ∘ 1 == f
    end
    
    cat = Category(src, target, relations ∪ identity);
    if checkComposability(cat, true)
        if checkComposition(cat, true)
            if checkAssociativity(cat, true)
                return cat
            end
        end
    end
end;

function checkComposability(c::Category, debug::Bool=false)
    for thisEquality in c.relations
        second, first = thisEquality.left.args 
        if second === 1 || first === 1
            continue
        end
        
        if c.src[second] != c.target[first]
            if debug
                println("composability violation")
                println(first,second)
                println(" ")
            end
            return false
        end
    end
    return true
end

# Compose arrows j and i and then simplify
function simplifyComposition(i::Symbol, j::Symbol, c::Category) :: Symbol
    expression = :($j ∘ $i) 

    g = EGraph(expression)
    saturate!(g, c.relations)
    simplified = extract!(g, astsize)
    return simplified
end

# Check that category c satisfies associativity by brute force
function checkAssociativity(c::Category, debug::Bool = false) :: Bool
    morphisms = keys(c.src)
 
    for i in morphisms
        for j in morphisms
            for k in morphisms
                if (c.target[i] == c.src[j]) && (c.target[j] == c.src[k])
                    leftAssocLeft = simplifyComposition(i, j, c)
                    leftAssoc = simplifyComposition(leftAssocLeft, k, c)
                    rightAssocRight = simplifyComposition(j, k, c)
                    rightAssoc = simplifyComposition(i, rightAssocRight, c)
                    if leftAssoc != rightAssoc
                        if debug
                            print("associativity violation: ")
                            println(i,j,k)
                            println(leftAssocLeft)
                            println(leftAssoc)
                            println(rightAssocRight)
                            println(rightAssoc)
                            println(" ")
                        end

                        return false
                    end
                end
            end
        end
    end

    return true
end;

#Check that the composition of any two arrows with matching sources and targets has a name by brute force
function checkComposition(c::Category, debug::Bool=false) :: Bool
    
    morphisms = keys(c.src)
    leftSides = Set([string(thisEquality.left) for thisEquality in c.relations])

    for i in morphisms
        for j in morphisms
            if c.target[i] == c.src[j]
                thisComposition = :($j ∘ $i)
                if !in(string(thisComposition), leftSides)
                    if debug
                        println("missing composition name: ")
                        println(i,j)
                        println(" ")
                    end
                    return false
                end
            end
        end
    end
    return true
end;

src = Dict(:f => 0, :g => 1, :h => 2, :i => 0, :k => 1, :m => 0, :n => 0)
target = Dict(:f => 1, :g => 2, :h => 3, :i => 2, :k => 3, :m => 3, :n => 3)

relations = @theory f begin
    :g ∘ :f == :i 
    :h ∘ :g == :k
    :h ∘ :i == :m 
    :k ∘ :f == :m 
end

myCat = categoryInit(src, target, relations);

using NBInclude
nbexport("categories.jl", "categories.ipynb")