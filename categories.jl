using Metatheory
using Metatheory.EGraphs
using Metatheory.Library

struct Category
    src::Dict
    target::Dict
    relations
end

src = Dict(:f => 0, :g => 1, :h => 2, :i => 0, :k => 1, :m => 0, :n => 0)
target = Dict(:f => 1, :g => 2, :h => 3, :i => 2, :k => 3, :m => 3, :n => 3)

relations = @theory f begin
    1 ∘ f == f 
    f ∘ 1 == f

    :g ∘ :f == :i 
    :h ∘ :g == :k
    :h ∘ :i == :m 
    :k ∘ :f == :m 
    
end

myCat = Category(src, target, relations);

function simplifyComposition(i, j, c::Category)
    expression = :($j ∘ $i) 

    g = EGraph(expression)
    saturate!(g, c.relations)
    simplified = extract!(g, astsize)
    return simplified
end

function checkAssociativity(c::Category, debug = false)
    #objects = union(Set(values(c.src)), Set(values(c.target)))
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
                            println(i,j,k)
                            println(leftAssocLeft)
                            println(leftAssoc)
                            println(rightAssocRight)
                            println(rightAssoc)
                        end

                        return false
                    end
                end
            end
        end
    end

    return true
end;

checkAssociativity(myCat, true)

using NBInclude
nbexport("categories.jl", "categories.ipynb")

#==
function checkComposition(c::Category)
    objects = union(Set(values(c.src)), Set(values(c.target)))
    morphisms = keys(c.src)
 
    for i in morphisms
     for j in morphisms
         if target[i] == src[j]
             thisComposition = :($j ∘ $i)
             println(thisComposition)
             for rule in c.relations
                 println(rule.left)
                 if rule.left == thisComposition
                     continue
                 end
             end
         end
     end
    end
 end
 ==#