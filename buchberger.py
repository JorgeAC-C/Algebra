"""
Base de Groebner Reducida - Algoritmo de Buchberger
Orden monomial: lexicografico (lex)
Representacion: polinomio = dict {(e1,e2,...,en): coeficiente}
"""

# ─────────────────────────────────────────
# 1. ORDEN LEXICOGRAFICO
# ─────────────────────────────────────────

def lex_mayor(a, b):
    """Devuelve True si el monomio a es mayor que b en orden lex."""
    for x, y in zip(a, b):
        if x > y: return True
        if x < y: return False
    return False

def termino_lider(p):
    """Devuelve el monomio lider (mayor en lex) de un polinomio."""
    return max(p.keys(), key=lambda m: m)

def coef_lider(p):
    """Devuelve el coeficiente del termino lider."""
    return p[termino_lider(p)]

def mono_lider(p):
    """Devuelve el monomio lider como tupla."""
    return termino_lider(p)

# ─────────────────────────────────────────
# 2. OPERACIONES CON POLINOMIOS
# ─────────────────────────────────────────

def limpiar(p):
    """Elimina terminos con coeficiente cero."""
    return {m: c for m, c in p.items() if abs(c) > 1e-10}

def suma(p, q):
    """Suma dos polinomios."""
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + c
    return limpiar(r)

def resta(p, q):
    """Resta dos polinomios."""
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) - c
    return limpiar(r)

def mult_monomio(p, mono, coef):
    """Multiplica un polinomio por un monomio*coef."""
    return {tuple(e + f for e, f in zip(m, mono)): c * coef
            for m, c in p.items()}

def normalizar(p):
    """Divide el polinomio por su coeficiente lider para que sea monico."""
    cl = coef_lider(p)
    return {m: c / cl for m, c in p.items()}

def divide_monomio(a, b):
    """
    Intenta dividir monomio a entre monomio b.
    Devuelve el cociente si b divide a, None en caso contrario.
    """
    cociente = tuple(x - y for x, y in zip(a, b))
    if all(e >= 0 for e in cociente):
        return cociente
    return None

# ─────────────────────────────────────────
# 3. DIVISION MULTIVARIADA
# ─────────────────────────────────────────

def division(f, lista_g):
    """
    Divide f entre la lista de polinomios lista_g.
    Devuelve (cocientes, resto).
    Algoritmo de division multivariada (Cox, Little, O'Shea, Cap. 2).
    """
    n = len(lista_g)
    cocientes = [{} for _ in range(n)]
    resto = {}
    p = dict(f)

    while p:
        lt_p = termino_lider(p)
        cl_p = p[lt_p]
        dividido = False

        for i, g in enumerate(lista_g):
            lt_g = termino_lider(g)
            cociente_mono = divide_monomio(lt_p, lt_g)
            if cociente_mono is not None:
                coef_div = cl_p / coef_lider(g)
                # Actualizamos cociente i
                cocientes[i][cociente_mono] = \
                    cocientes[i].get(cociente_mono, 0) + coef_div
                # Restamos lt_g * coef_div * g de p
                p = resta(p, mult_monomio(g, cociente_mono, coef_div))
                dividido = True
                break

        if not dividido:
            # El termino lider no es divisible por ningun g_i -> va al resto
            resto[lt_p] = resto.get(lt_p, 0) + cl_p
            del p[lt_p]
            p = limpiar(p)

    return cocientes, limpiar(resto)

# ─────────────────────────────────────────
# 4. S-POLINOMIO
# ─────────────────────────────────────────

def mcm_monomio(a, b):
    """Minimo comun multiplo de dos monomios."""
    return tuple(max(x, y) for x, y in zip(a, b))

def s_polinomio(f, g):
    """
    Calcula el S-polinomio de f y g.
    S(f,g) = (mcm/lt(f))*f - (mcm/lt(g))*g
    """
    lt_f = mono_lider(f)
    lt_g = mono_lider(g)
    mcm = mcm_monomio(lt_f, lt_g)

    mono_f = tuple(x - y for x, y in zip(mcm, lt_f))
    mono_g = tuple(x - y for x, y in zip(mcm, lt_g))

    termino_f = mult_monomio(f, mono_f, 1 / coef_lider(f))
    termino_g = mult_monomio(g, mono_g, 1 / coef_lider(g))

    return resta(termino_f, termino_g)

# ─────────────────────────────────────────
# 5. ALGORITMO DE BUCHBERGER
# ─────────────────────────────────────────

def buchberger(generadores):
    """
    Calcula una base de Groebner del ideal generado por 'generadores'.
    Implementacion del algoritmo de Buchberger (Cox, Little, O'Shea, Cap. 2).
    """
    G = list(generadores)
    pares_pendientes = [(i, j) for i in range(len(G))
                                for j in range(i+1, len(G))]

    while pares_pendientes:
        i, j = pares_pendientes.pop(0)
        s = s_polinomio(G[i], G[j])
        _, r = division(s, G)

        if r:  # Si el resto no es cero, lo añadimos a la base
            pares_pendientes += [(k, len(G)) for k in range(len(G))]
            G.append(r)

    return G

# ─────────────────────────────────────────
# 6. REDUCCION A BASE REDUCIDA
# ─────────────────────────────────────────

def base_reducida(G):
    """
    A partir de una base de Groebner G, obtiene la base reducida:
    1. Elimina polinomios cuyo termino lider es divisible por el de otro
    2. Reduce cada polinomio respecto al resto de la base
    3. Normaliza para que cada polinomio sea monico
    """
    # Paso 1: eliminar redundantes
    G = [normalizar(g) for g in G]
    minimal = []
    for i, g in enumerate(G):
        lt_g = mono_lider(g)
        redundante = False
        for j, h in enumerate(G):
            if i != j:
                lt_h = mono_lider(h)
                if divide_monomio(lt_g, lt_h) is not None:
                    redundante = True
                    break
        if not redundante:
            minimal.append(g)

    # Paso 2: reducir cada elemento respecto a los demas
    reducida = []
    for i, g in enumerate(minimal):
        resto_base = [h for j, h in enumerate(minimal) if j != i]
        _, r = division(g, resto_base)
        if r:
            reducida.append(normalizar(r))

    return reducida

# ─────────────────────────────────────────
# 7. UTILIDADES DE PRESENTACION
# ─────────────────────────────────────────

def poly_str(p, variables):
    """Convierte un polinomio a string legible."""
    if not p:
        return "0"
    terminos = []
    for mono in sorted(p.keys(), reverse=True):
        c = p[mono]
        parte_mono = ""
        for i, e in enumerate(mono):
            if e == 1:
                parte_mono += variables[i]
            elif e > 1:
                parte_mono += f"{variables[i]}^{e}"
        if parte_mono == "":
            terminos.append(f"{c:.4g}")
        elif abs(c - 1) < 1e-10:
            terminos.append(parte_mono)
        elif abs(c + 1) < 1e-10:
            terminos.append(f"-{parte_mono}")
        else:
            terminos.append(f"{c:.4g}{parte_mono}")
    return " + ".join(terminos).replace("+ -", "- ")

# ─────────────────────────────────────────
# 8. EJEMPLO DE USO
# ─────────────────────────────────────────

if __name__ == "__main__":
    # Variables: x, y
    # Polinomios: f1 = x^2 + y,  f2 = x*y - 1
    # Representacion: {(exp_x, exp_y): coeficiente}

    variables = ['x', 'y']

    f1 = {(2,0): 1, (0,1): 1}        # x^2 + y
    f2 = {(1,1): 1, (0,0): -1}       # xy - 1

    generadores = [f1, f2]

    print("Generadores:")
    for f in generadores:
        print(" ", poly_str(f, variables))

    G = buchberger(generadores)
    print("\nBase de Groebner (sin reducir):")
    for g in G:
        print(" ", poly_str(g, variables))

    R = base_reducida(G)
    print("\nBase de Groebner REDUCIDA:")
    for r in R:
        print(" ", poly_str(r, variables))
