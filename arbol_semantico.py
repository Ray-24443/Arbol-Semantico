
import tkinter as tk
from tkinter import ttk, messagebox
import re
import unicodedata

# ============================================================
# 1. FUNCIONES DE TEXTO Y ANALISIS DEL LENGUAJE
# ============================================================

def normalizar(texto):
    """Convierte el texto a minusculas y elimina acentos."""
    texto = texto.lower().strip()
    texto = unicodedata.normalize("NFD", texto)
    return "".join(
        c for c in texto
        if unicodedata.category(c) != "Mn"
    )


def dividir(texto, separador):
    """Divide una expresion sin separar dentro de parentesis."""
    profundidad = 0
    texto_n = normalizar(texto)
    sep_n = normalizar(separador)

    for i, caracter in enumerate(texto):
        if caracter == "(":
            profundidad += 1
        elif caracter == ")":
            profundidad -= 1

        if profundidad == 0:
            if texto_n[i:].startswith(sep_n):
                antes = texto_n[:i]
                despues = texto_n[i + len(sep_n):]

                # Evita separar palabras que contienen el conector.
                if (not antes or antes[-1].isspace()) and (
                    not despues or despues[0].isspace()
                ):
                    return texto[:i].strip(), texto[
                        i + len(separador):
                    ].strip()

    return None


# ============================================================
# 2. CONVERTIR FRASES EN EXPRESIONES LOGICAS
#
# Representacion:
# ("atom", "es de dia")
# ("not", expresion)
# ("and", izquierda, derecha)
# ("or", izquierda, derecha)
# ("imp", antecedente, consecuente)
# ("iff", izquierda, derecha)
# ============================================================

def analizar(texto):
    texto = texto.strip()

    # Elimina parentesis exteriores equilibrados.
    while texto.startswith("(") and texto.endswith(")"):
        profundidad = 0
        valido = True

        for i, c in enumerate(texto):
            if c == "(":
                profundidad += 1
            elif c == ")":
                profundidad -= 1
            if profundidad == 0 and i < len(texto) - 1:
                valido = False
                break

        if valido:
            texto = texto[1:-1].strip()
        else:
            break

    if not texto:
        raise ValueError("Hay una proposicion vacia.")

    # Si A, entonces B
    coincidencia = re.match(
        r"^si\s+(.+?),?\s+entonces\s+(.+)$",
        texto, re.IGNORECASE
    )
    if coincidencia:
        return (
            "imp",
            analizar(coincidencia.group(1).rstrip(" ,")),
            analizar(coincidencia.group(2))
        )

    # A si y solo si B
    partes = dividir(texto, " si y solo si ")
    if partes:
        return ("iff", analizar(partes[0]), analizar(partes[1]))

    # A implica B
    partes = dividir(texto, " implica ")
    if partes:
        return ("imp", analizar(partes[0]), analizar(partes[1]))

    # Conector Y
    partes = dividir(texto, " y ")
    if partes:
        return ("and", analizar(partes[0]), analizar(partes[1]))

    # Conector O
    partes = dividir(texto, " o ")
    if partes:
        return ("or", analizar(partes[0]), analizar(partes[1]))

    # Negacion: "no A"
    if normalizar(texto).startswith("no "):
        return ("not", analizar(texto[3:]))

    # Hecho simple: se conserva como un atomo.
    return ("atom", " ".join(normalizar(texto).split()))


# ============================================================
# 3. ASIGNAR LETRAS A LAS PROPOSICIONES SIMPLES
# ============================================================

def atomos(expr, resultado):
    """Recopila los atomos, sin duplicar proposiciones."""
    if expr[0] == "atom":
        if expr[1] not in resultado:
            resultado.append(expr[1])
    elif expr[0] == "not":
        atomos(expr[1], resultado)
    else:
        atomos(expr[1], resultado)
        atomos(expr[2], resultado)


def mostrar_formula(expr, letras):
    """Convierte el arbol interno a notacion logica."""
    tipo = expr[0]

    if tipo == "atom":
        return letras[expr[1]]

    if tipo == "not":
        return "¬" + mostrar_formula(expr[1], letras)

    simbolos = {
        "and": "∧",
        "or": "∨",
        "imp": "→",
        "iff": "↔"
    }

    izquierda = mostrar_formula(expr[1], letras)
    derecha = mostrar_formula(expr[2], letras)

    return f"({izquierda} {simbolos[tipo]} {derecha})"


# ============================================================
# 4. REGLAS DE EXPANSION DEL TABLEAU
#
# Cada formula lleva un signo:
# True  = la formula debe ser verdadera.
# False = la formula debe ser falsa.
# ============================================================

def desarrollar(ramas, atomos_texto):
    finales = []
    pendientes = list(ramas)
    limite = 5000
    iteraciones = 0

    while pendientes and iteraciones < limite:
        iteraciones += 1
        rama = pendientes.pop()
        asignaciones = {}
        contradiccion = False

        # Detectar p y ¬p en la misma rama.
        for expr, signo in rama:
            if expr[0] == "atom":
                nombre = expr[1]
                if nombre in asignaciones:
                    if asignaciones[nombre] != signo:
                        contradiccion = True
                        break
                else:
                    asignaciones[nombre] = signo

        if contradiccion:
            finales.append((rama, "CERRADA"))
            continue

        # Encontrar una formula compuesta aun no desarrollada.
        elegido = None

        for i, (expr, signo) in enumerate(rama):
            if expr[0] != "atom" and (i, signo) not in rama_aplicadas(rama):
                elegido = (i, expr, signo)
                break

        # La funcion auxiliar usa marcas incluidas en la rama.
        # Si no quedan formulas compuestas, la rama esta abierta.
        if elegido is None:
            finales.append((rama, "ABIERTA"))
            continue

        i, expr, signo = elegido
        base = rama[:i] + rama[i + 1:]
        tipo = expr[0]

        # Normalizar negacion cambiando el signo.
        if tipo == "not":
            pendientes.append(base + [(expr[1], not signo)])
            continue

        a, b = expr[1], expr[2]

        # Expansiones que agregan ambas formulas a una rama.
        ambas = None
        alternativas = None

        if tipo == "and":
            if signo:
                ambas = [(a, True), (b, True)]
            else:
                alternativas = [[(a, False)], [(b, False)]]

        elif tipo == "or":
            if signo:
                alternativas = [[(a, True)], [(b, True)]]
            else:
                ambas = [(a, False), (b, False)]

        elif tipo == "imp":
            if signo:
                alternativas = [[(a, False)], [(b, True)]]
            else:
                ambas = [(a, True), (b, False)]

        elif tipo == "iff":
            if signo:
                alternativas = [
                    [(a, True), (b, True)],
                    [(a, False), (b, False)]
                ]
            else:
                alternativas = [
                    [(a, True), (b, False)],
                    [(a, False), (b, True)]
                ]

        if ambas is not None:
            pendientes.append(base + ambas)
        elif alternativas is not None:
            for alternativa in alternativas:
                pendientes.append(base + alternativa)

    return finales


def rama_aplicadas(rama):
    """
    Se sustituye por un seguimiento explicito en la version
    extendida. Esta funcion permite reconocer formulas usadas
    mediante la lista de indices desarrollados.
    """
    return set()


# ============================================================
# 5. PRESENTACION DE RESULTADOS
# ============================================================

def ejecutar():
    entrada = caja.get("1.0", tk.END).strip()

    if not entrada:
        messagebox.showwarning(
            "Faltan reglas",
            "Escribe al menos una regla."
        )
        return

    try:
        reglas_texto = [
            linea.strip()
            for linea in entrada.splitlines()
            if linea.strip()
        ]

        reglas = [analizar(r) for r in reglas_texto]

        lista_atomos = []
        for regla in reglas:
            atomos(regla, lista_atomos)

        letras = {
            nombre: chr(112 + i)
            for i, nombre in enumerate(lista_atomos)
        }

        salida.delete("1.0", tk.END)
        salida.insert(tk.END, "1. BASE DE CONOCIMIENTO\n\n")

        for i, regla in enumerate(reglas):
            salida.insert(
                tk.END,
                f"R{i + 1}: {mostrar_formula(regla, letras)}\n"
            )

        salida.insert(tk.END, "\n2. TABLA DE ATOMOS\n\n")
        for nombre, letra in letras.items():
            salida.insert(tk.END, f"{letra} = {nombre}\n")

        salida.insert(
            tk.END,
            "\n3. ARBOL SEMANTICO\n\n"
            "Todas las reglas se suponen verdaderas.\n\n"
        )

        # Cada regla comienza marcada como verdadera.
        ramas = [[(regla, True) for regla in reglas]]
        finales = desarrollar(ramas, lista_atomos)

        abiertas = 0
        cerradas = 0

        for numero, (rama, estado) in enumerate(finales, 1):
            salida.insert(
                tk.END,
                f"Rama {numero} [{estado}]\n"
            )

            for expr, signo in rama:
                simbolo = "T" if signo else "F"
                salida.insert(
                    tk.END,
                    f"   {simbolo}: "
                    f"{mostrar_formula(expr, letras)}\n"
                )

            if estado == "CERRADA":
                cerradas += 1
                salida.insert(tk.END, "   ✕ CONTRADICCION\n\n")
            else:
                abiertas += 1
                valores = {}
                for expr, signo in rama:
                    if expr[0] == "atom":
                        valores[expr[1]] = signo

                salida.insert(tk.END, "   MODELO:\n")
                for nombre, letra in letras.items():
                    valor = valores.get(nombre, None)
                    texto_valor = (
                        "V" if valor is True else
                        "F" if valor is False else "Indeterminado"
                    )
                    salida.insert(
                        tk.END,
                        f"      {letra} = {texto_valor}\n"
                    )
                salida.insert(tk.END, "\n")

        salida.insert(tk.END, "4. CONCLUSION\n\n")

        if abiertas:
            salida.insert(
                tk.END,
                "La base de conocimiento es SATISFACIBLE.\n"
                f"Ramas abiertas: {abiertas}\n"
                f"Ramas cerradas: {cerradas}\n"
            )
        else:
            salida.insert(
                tk.END,
                "La base de conocimiento es INSATISFACIBLE.\n"
                "Todas las ramas se cerraron.\n"
            )

    except Exception as error:
        messagebox.showerror(
            "Error de analisis",
            f"No se pudieron interpretar las reglas:\n{error}"
        )


# ============================================================
# 6. INTERFAZ GRAFICA
# ============================================================

ventana = tk.Tk()
ventana.title("Constructor de Arboles Semanticos")
ventana.geometry("950x720")
ventana.minsize(700, 500)

titulo = ttk.Label(
    ventana,
    text="LOGICA PROPOSICIONAL - ARBOL SEMANTICO",
    font=("Arial", 16, "bold")
)
titulo.pack(pady=12)

instruccion = ttk.Label(
    ventana,
    text="Escribe una regla por linea, en espanol."
)
instruccion.pack()

caja = tk.Text(ventana, height=7, font=("Arial", 11))
caja.pack(fill="x", padx=15, pady=8)

caja.insert(
    "1.0",
    "Si es de dia, entonces voy a trabajar\n"
    "Si llueve, entonces no voy a trabajar\n"
    "Es de dia"
)

boton = ttk.Button(
    ventana,
    text="Construir arbol semantico",
    command=ejecutar
)
boton.pack(pady=8)

marco = ttk.Frame(ventana)
marco.pack(fill="both", expand=True, padx=15, pady=8)

barra = ttk.Scrollbar(marco)
barra.pack(side="right", fill="y")

salida = tk.Text(
    marco,
    font=("Consolas", 11),
    wrap="word",
    yscrollcommand=barra.set
)
salida.pack(side="left", fill="both", expand=True)
barra.config(command=salida.yview)

ventana.mainloop()
