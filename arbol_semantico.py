import re
import tkinter as tk
from tkinter import messagebox, scrolledtext
import unicodedata
from dataclasses import dataclass, field

import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


# ============================================================
# 1. UTILIDADES
# ============================================================

def normalizar(texto):
    """Pasa a minusculas y elimina acentos."""
    texto = texto.lower().strip()
    return "".join(
        c for c in unicodedata.normalize("NFD", texto)
        if unicodedata.category(c) != "Mn"
    )


def quitar_bordes(texto):
    """Elimina parentesis exteriores que cubren toda la formula."""
    texto = texto.strip()

    while texto.startswith("(") and texto.endswith(")"):
        nivel = 0
        valido = True

        for i, c in enumerate(texto):
            if c == "(":
                nivel += 1
            elif c == ")":
                nivel -= 1

            if nivel == 0 and i < len(texto) - 1:
                valido = False
                break

        if not valido:
            break

        texto = texto[1:-1].strip()

    return texto


def dividir(texto, patrones):
    """
    Busca el primer conector fuera de parentesis.
    Devuelve las partes izquierda y derecha.
    """
    norm = normalizar(texto)
    nivel = 0
    i = 0

    while i < len(norm):
        if norm[i] == "(":
            nivel += 1
            i += 1
            continue

        if norm[i] == ")":
            nivel -= 1
            i += 1
            continue

        if nivel == 0:
            for patron in patrones:
                coincidencia = re.match(patron, norm[i:])

                if coincidencia:
                    # Los patrones empiezan y terminan
                    # en espacios para separar palabras.
                    longitud = coincidencia.end()
                    izquierda = texto[:i]
                    derecha = texto[i + longitud:]

                    if izquierda.strip() and derecha.strip():
                        return izquierda.strip(), derecha.strip()

        i += 1

    return None


# ============================================================
# 2. FORMULAS LOGICAS
# ============================================================

@dataclass(frozen=True)
class Formula:
    tipo: str
    izquierda: object = None
    derecha: object = None
    nombre: str = ""
    original: str = field(default="", compare=False, hash=False)


def parsear(texto):
    """Convierte texto en español a una formula logica."""

    texto = quitar_bordes(texto.strip().rstrip(".;"))

    if not texto:
        raise ValueError("Se encontro una proposicion vacia.")

    norm = normalizar(texto)

    # Condicional: Si A, entonces B
    m = re.match(
        r"^\s*si\s+(.+?),?\s+entonces\s+(.+)\s*$",
        norm
    )

    if m:
        # Los acentos no alteran las posiciones en el texto habitual.
        a, b = m.span(1), m.span(2)
        return Formula(
            "implica",
            parsear(texto[a[0]:a[1]]),
            parsear(texto[b[0]:b[1]])
        )

    # Bicondicional
    partes = dividir(
        texto,
        [r"\s+si y solo si\s+", r"\s+sii\s+", r"\s+↔\s+"]
    )
    if partes:
        return Formula("bicond", parsear(partes[0]), parsear(partes[1]))

    # Implicacion
    partes = dividir(
        texto,
        [r"\s+implica\s+", r"\s+→\s+"]
    )
    if partes:
        return Formula("implica", parsear(partes[0]), parsear(partes[1]))

    # Disyuncion
    partes = dividir(
        texto,
        [r"\s+o\s+", r"\s+u\s+", r"\s+∨\s+"]
    )
    if partes:
        return Formula("or", parsear(partes[0]), parsear(partes[1]))

    # Conjuncion
    partes = dividir(
        texto,
        [
            r"\s+y\s+",
            r"\s+pero\s+",
            r"\s+aunque\s+",
            r"\s+∧\s+"
        ]
    )
    if partes:
        return Formula("and", parsear(partes[0]), parsear(partes[1]))

    # Negacion
    if norm.startswith("no "):
        return Formula("not", izquierda=parsear(texto[3:]))

    prefijo = "es falso que "
    if norm.startswith(prefijo):
        return Formula(
            "not",
            izquierda=parsear(texto[len(prefijo):])
        )

    if texto.startswith("¬"):
        return Formula("not", izquierda=parsear(texto[1:]))

    # Proposicion atomica
    return Formula(
        "atom",
        nombre=normalizar(texto),
        original=texto.strip()
    )


def recoger_atomos(formula, resultado):
    """Guarda las proposiciones atomicas sin duplicarlas."""
    if formula.tipo == "atom":
        resultado.setdefault(formula.nombre, formula.original)
        return

    recoger_atomos(formula.izquierda, resultado)

    if formula.derecha is not None:
        recoger_atomos(formula.derecha, resultado)


def imprimir_formula(formula, simbolos):
    """Convierte una formula a notacion simbolica."""

    if formula.tipo == "atom":
        return simbolos[formula.nombre]

    if formula.tipo == "not":
        hijo = formula.izquierda
        texto = imprimir_formula(hijo, simbolos)

        if hijo.tipo == "atom" or hijo.tipo == "not":
            return "¬" + texto

        return "¬(" + texto + ")"

    operadores = {
        "and": "∧",
        "or": "∨",
        "implica": "→",
        "bicond": "↔"
    }

    a = imprimir_formula(formula.izquierda, simbolos)
    b = imprimir_formula(formula.derecha, simbolos)

    return f"({a} {operadores[formula.tipo]} {b})"


# ============================================================
# 3. TABLEAU SEMANTICO
# ============================================================

@dataclass
class Rama:
    # Cada elemento contiene (formula, valor de verdad).
    entradas: list = field(default_factory=list)
    aplicadas: set = field(default_factory=set)
    estado: str = "abierta"
    motivo: str = ""


def clave(formula, verdad):
    """Identifica una formula con su valor de verdad."""
    return formula, verdad


def agregar(rama, formula, verdad):
    """Evita repetir una formula con el mismo valor."""
    elemento = clave(formula, verdad)

    if elemento not in rama.entradas:
        rama.entradas.append(elemento)


def comprobar_contradiccion(rama):
    """
    Detecta p y no p en una misma rama.
    Tambien reconoce la negacion de un atomo.
    """
    valores = {}

    for formula, verdad in rama.entradas:
        if formula.tipo == "atom":
            nombre = formula.nombre
            valor = verdad

        elif (
            formula.tipo == "not"
            and formula.izquierda.tipo == "atom"
        ):
            nombre = formula.izquierda.nombre
            valor = not verdad

        else:
            continue

        if nombre in valores and valores[nombre] != valor:
            return True, f"Contradiccion en {nombre}"

        valores[nombre] = valor

    return False, ""


def expandir(formula, verdad):
    """
    Reglas correctas de expansion del tableau.

    Cada lista interna agrega formulas a una misma rama.
    Listas diferentes generan ramas alternativas.
    """
    tipo = formula.tipo
    a = formula.izquierda
    b = formula.derecha

    if tipo == "atom":
        return None

    if tipo == "not":
        return [[(a, not verdad)]]

    if tipo == "and":
        if verdad:
            return [[(a, True), (b, True)]]
        return [[(a, False)], [(b, False)]]

    if tipo == "or":
        if verdad:
            return [[(a, True)], [(b, True)]]
        return [[(a, False), (b, False)]]

    if tipo == "implica":
        if verdad:
            return [[(a, False)], [(b, True)]]
        return [[(a, True), (b, False)]]

    if tipo == "bicond":
        if verdad:
            return [
                [(a, True), (b, True)],
                [(a, False), (b, False)]
            ]

        return [
            [(a, True), (b, False)],
            [(a, False), (b, True)]
        ]

    return None


def construir_arbol(formulas):
    """
    Expande las ramas pendientes.
    Prioriza las fórmulas que no generan nuevas ramas para optimizar el árbol.
    Cierra las contradicciones en cuanto aparecen.
    """
    inicial = Rama()

    for formula in formulas:
        agregar(inicial, formula, True)

    ramas = [inicial]
    max_pasos = 500

    for _ in range(max_pasos):
        cambio = False
        nuevas = []

        for rama in ramas:

            if rama.estado == "cerrada":
                nuevas.append(rama)
                continue

            cerrada, motivo = comprobar_contradiccion(rama)

            if cerrada:
                rama.estado = "cerrada"
                rama.motivo = motivo
                nuevas.append(rama)
                continue

            # Buscar todas las fórmulas pendientes
            pendientes = []
            for elemento in rama.entradas:
                formula, verdad = elemento
                if formula.tipo == "atom":
                    continue
                if elemento not in rama.aplicadas:
                    pendientes.append(elemento)

            if not pendientes:
                rama.estado = "abierta"
                nuevas.append(rama)
                continue

            cambio = True
            
            # --- LÓGICA DE PRIORIDAD ---
            # Identificamos si una fórmula NO va a crear bifurcaciones
            def es_ramificante(elem):
                f, v = elem
                if f.tipo == "not": return False
                if f.tipo == "and" and v is True: return False
                if f.tipo == "or" and v is False: return False
                if f.tipo == "implica" and v is False: return False
                return True

            # Ordenamos para procesar primero las que no ramifican
            pendientes.sort(key=es_ramificante)
            pendiente = pendientes[0]
            # ---------------------------

            formula, verdad = pendiente
            alternativas = expandir(formula, verdad)

            rama.aplicadas.add(pendiente)

            if alternativas is None:
                nuevas.append(rama)
                continue

            for alternativa in alternativas:
                nueva = Rama(
                    entradas=list(rama.entradas),
                    aplicadas=set(rama.aplicadas)
                )

                for f, v in alternativa:
                    agregar(nueva, f, v)

                cerrada, motivo = comprobar_contradiccion(nueva)

                if cerrada:
                    nueva.estado = "cerrada"
                    nueva.motivo = motivo

                nuevas.append(nueva)

        ramas = nuevas

        if not cambio:
            break

    return ramas


# ============================================================
# 4. DIBUJAR EL ARBOL
# ============================================================

def dibujar_arbol(contenedor, ramas, simbolos):
    for widget in contenedor.winfo_children():
        widget.destroy()

    cantidad = len(ramas)
    ancho = max(10, cantidad * 2.4)

    figura = plt.Figure(figsize=(ancho, 7), dpi=100)
    ax = figura.add_subplot(111)
    ax.axis("off")
    ax.set_title(
        "ARBOL SEMANTICO",
        fontsize=15,
        fontweight="bold"
    )

    centro = (cantidad - 1) / 2

    ax.text(
        centro, 0, "PREMISAS",
        ha="center", va="center",
        bbox=dict(boxstyle="round", fc="#dceaf7", ec="#355c7d")
    )

    profundidad = 1

    for i, rama in enumerate(ramas):
        x = i
        previo_y = 0

        # Evitar mostrar duplicados en la rama
        vistos = set()
        elementos = []

        for formula, verdad in rama.entradas:
            texto = (
                ("T " if verdad else "F ")
                + imprimir_formula(formula, simbolos)
            )

            if texto not in vistos:
                vistos.add(texto)
                elementos.append(texto)

        for nivel, texto in enumerate(elementos, start=1):
            y = -nivel
            profundidad = max(profundidad, nivel + 2)

            ax.plot(
                [centro if nivel == 1 else x, x],
                [previo_y - 0.12, y + 0.12],
                color="#657786",
                linewidth=1
            )

            ax.text(
                x, y, texto,
                ha="center", va="center",
                fontsize=8,
                bbox=dict(
                    boxstyle="round,pad=0.3",
                    fc="#f4f6f8",
                    ec="#8a969f"
                )
            )

            previo_y = y

        y_final = -(len(elementos) + 1)

        if rama.estado == "cerrada":
            etiqueta = "CERRADA X"
            fondo = "#f8d7da"
            borde = "#b02a37"
        else:
            etiqueta = "ABIERTA"
            fondo = "#d4edda"
            borde = "#198754"

        ax.plot(
            [x, x],
            [previo_y - 0.12, y_final + 0.12],
            color=borde,
            linewidth=1.3
        )

        ax.text(
            x, y_final, etiqueta,
            ha="center", va="center",
            fontsize=9, fontweight="bold",
            bbox=dict(
                boxstyle="round,pad=0.4",
                fc=fondo, ec=borde
            )
        )

    ax.set_xlim(-1, max(1, cantidad))
    ax.set_ylim(-(profundidad + 0.5), 0.8)
    figura.tight_layout()

    canvas = FigureCanvasTkAgg(figura, master=contenedor)
    canvas.draw()
    canvas.get_tk_widget().pack(fill="both", expand=True)

    return figura


# ============================================================
# 5. ANALIZAR PREMISAS
# ============================================================

def analizar():
    texto = entrada.get("1.0", tk.END).strip()

    if not texto:
        messagebox.showwarning(
            "Aviso", "Escribe al menos una premisa."
        )
        return

    lineas = [
        linea.strip()
        for linea in texto.splitlines()
        if linea.strip()
    ]

    try:
        formulas = [parsear(linea) for linea in lineas]
    except Exception as error:
        messagebox.showerror(
            "Error de interpretacion",
            str(error)
        )
        return

    atomos = {}
    for formula in formulas:
        recoger_atomos(formula, atomos)

    letras = "pqrstuvwxyzabcdefghijklmno"
    simbolos = {
        nombre: letras[i] if i < len(letras) else f"p{i+1}"
        for i, nombre in enumerate(atomos)
    }

    ramas = construir_arbol(formulas)

    abiertas = sum(r.estado == "abierta" for r in ramas)
    cerradas = sum(r.estado == "cerrada" for r in ramas)

    salida.delete("1.0", tk.END)

    salida.insert(tk.END, "SIMBOLIZACION DE LAS PREMISAS\n")
    salida.insert(tk.END, "-" * 38 + "\n")

    for i, formula in enumerate(formulas, start=1):
        salida.insert(
            tk.END,
            f"P{i}: {lineas[i-1]}\n"
            f"    {imprimir_formula(formula, simbolos)}\n\n"
        )

    salida.insert(tk.END, "PROPOSICIONES ATOMICAS\n")
    for nombre, original in atomos.items():
        salida.insert(
            tk.END,
            f"{simbolos[nombre]} = {original}\n"
        )

    salida.insert(tk.END, "\nRESULTADO DEL TABLEAU\n")
    salida.insert(tk.END, f"Ramas abiertas: {abiertas}\n")
    salida.insert(tk.END, f"Ramas cerradas: {cerradas}\n")

    if abiertas:
        salida.insert(
            tk.END,
            "\nCONCLUSION: PREMISAS CONSISTENTES.\n"
            "Existe al menos una rama abierta.\n"
        )
    else:
        salida.insert(
            tk.END,
            "\nCONCLUSION: PREMISAS INCONSISTENTES.\n"
            "Todas las ramas se cerraron.\n"
        )

    dibujar_arbol(marco_arbol, ramas, simbolos)


# ============================================================
# 6. INTERFAZ GRAFICA
# ============================================================

ventana = tk.Tk()
ventana.title("Logica I - Arbol semantico")
ventana.geometry("1200x850")
ventana.minsize(850, 600)

tk.Label(
    ventana,
    text="ARBOL SEMANTICO DE LOGICA PROPOSICIONAL",
    font=("Arial", 15, "bold")
).pack(pady=8)

tk.Label(
    ventana,
    text=(
        "Escribe una premisa por linea. "
        "Usa conectores como y, o, no, implica, "
        "si... entonces, si y solo si."
    ),
    wraplength=1000
).pack()

entrada = scrolledtext.ScrolledText(
    ventana, height=5, font=("Arial", 11), wrap=tk.WORD
)
entrada.pack(fill="x", padx=12, pady=6)

entrada.insert(
    tk.END,
    "Estudio o trabajo\n"
    "No estudio"
)

tk.Button(
    ventana,
    text="Analizar y mostrar arbol",
    command=analizar,
    font=("Arial", 11, "bold"),
    bg="#dceaf7",
    padx=12, pady=5
).pack(pady=4)

salida = scrolledtext.ScrolledText(
    ventana, height=10, font=("Consolas", 10), wrap=tk.WORD
)
salida.pack(fill="x", padx=12, pady=5)

marco_arbol = tk.Frame(ventana, bd=1, relief="sunken")
marco_arbol.pack(
    fill="both", expand=True, padx=12, pady=(2, 10)
)

ventana.after(300, analizar)
ventana.mainloop()