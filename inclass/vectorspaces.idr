interface Group a where
    (*)   : a -> a -> a
    i     : a
    assoc : {x : a} -> {y : a} -> {z : a} -> (x * y) * z = x * (y * z)
    i1    : {x : a} -> i * x = x
    i2    : {x : a} -> x * i = x
    inv   : (x : a) -> (x' : a ** (x' * x = i))

Group Double where
    (*) a b = a + b
    i = 0
    assoc = ?
    i1 = Refl
    i2 = ?
    inv x = ?

interface Field f where
    plusf : f -> f -> f
    multf : f -> f -> f

-- interface Field f => VecSpace a f where
