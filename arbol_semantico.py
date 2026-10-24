
import re
import tkinter as tk
from tkinter import messagebox, scrolledtext
import unicodedata
from dataclasses import dataclass, field

import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


# ============================================================
# 1. UTILIDADES PARA LEER PROPOSICIONES EN ESPAÑOL
# ============================================================

def normalizar(texto):
    """Convierte a minusculas y elimina acentos."""
    texto = texto.lower().strip()
    return "".join(
        c for c in unicodedata.normalize("NFD", texto)
        if unicodedata.category(c) != "Mn"
    )


def quitar_bordes(texto):
    texto = texto.strip()

    while len(texto) >= 2 and texto[0] == "(" and texto[-1] == ")":
        nivel = 0
        cubre_todo = True

        for i, c in enumerate(texto):
            if c == "(":
                nivel += 1
            elif c == ")":
                nivel -= 1

                if nivel == 0 and i != len(texto) - 1:
                    cubre_todo = False
                    break

        if cubre_todo:
            texto = texto[1:-1].strip()
        else:
            break

    return texto


def buscar_conector(texto, conectores):
    """Busca conectores logicos fuera de parentesis."""
    original = texto
    norm = normalizar(original)
    nivel = 0
    i = 0

    while i < len(original):
        if original[i] == "(":
            nivel += 1
            i += 1
            continue

        if original[i] == ")":
            nivel -= 1
            i += 1
            continue

        if nivel == 0:
            for conector in conectores:
                cn = normalizar(conector)

                if norm[i:i + len(cn)] == cn:
                    antes_ok = (
                        i == 0 or not norm[i - 1].isalnum()
                    )

                    despues = i + len(cn)

                    despues_ok = (
                        despues >= len(norm)
                        or not norm[despues].isalnum()
                    )

                    if antes_ok and despues_ok:
                        return i, original[i:i + len(cn)]

        i += 1

    return None


@dataclass(frozen=True)
class Formula:
    tipo: str
    izquierda: object = None
    derecha: object = None
    nombre: str = ""


def parsear(texto):
    """Convierte una proposicion escrita en una formula logica."""

    texto = quitar_bordes(texto.strip().rstrip(".;"))

    if not texto:
        raise ValueError("Hay una proposicion vacia.")

    norm = normalizar(texto)

    # Condicional: Si A, entonces B
    m = re.match(
        r"^\s*si\s+(.+?),?\s+entonces\s+(.+)\s*$",
        texto,
        flags=re.IGNORECASE
    )

    if m:
        return Formula(
            "implica",
            parsear(m.group(1)),
            parsear(m.group(2))
        )

    # Bicondicional
    encontrado = buscar_conector(
        texto, [" si y solo si ", " sii "]
    )

    if encontrado:
        pos, con = encontrado
        return Formula(
            "bicond",
            parsear(texto[:pos]),
            parsear(texto[pos + len(con):])
        )

    # Implicacion
    encontrado = buscar_conector(texto, [" implica "])

    if encontrado:
        pos, con = encontrado
        return Formula(
            "implica",
            parsear(texto[:pos]),
            parsear(texto[pos + len(con):])
        )

    # Disyuncion
    encontrado = buscar_conector(texto, [" o ", " u "])

    if encontrado:
        pos, con = encontrado
        return Formula(
            "or",
            parsear(texto[:pos]),
            parsear(texto[pos + len(con):])
        )

    # Conjuncion
    encontrado = buscar_conector(
        texto, [" y ", " pero ", " aunque "]
    )

    if encontrado:
        pos, con = encontrado
        return Formula(
            "and",
            parsear(texto[:pos]),
            parsear(texto[pos + len(con):])
        )

    # Negacion
    if norm.startswith("no "):
        return Formula("not", parsear(texto[3:]))

    if norm.startswith("es falso que "):
        return Formula(
            "not",
            parsear(texto[len("es falso que "):])
        )

    if texto.startswith("¬"):
        return Formula("not", parsear(texto[1:]))

    # Simbolos logicos
    for simbolo, tipo in [
        ("→", "implica"),
        ("∧", "and"),
        ("∨", "or"),
        ("↔", "bicond")
    ]:
        if simbolo in texto:
            pos = texto.find(simbolo)
            return Formula(
                tipo,
                parsear(texto[:pos]),
                parsear(texto[pos + 1:])
            )

    # Proposicion simple
    return Formula("atom", nombre=texto.strip())


def imprimir_formula(f):
    if f.tipo == "atom":
        return f.nombre

    if f.tipo == "not":
        hijo = imprimir_formula(f.izquierda)

        if f.izquierda.tipo == "atom":
            return "¬" + hijo

        return "¬(" + hijo + ")"

    simbolos = {
        "and": "∧",
        "or": "∨",
        "implica": "→",
        "bicond": "↔"
    }

    return (
        "("
        + imprimir_formula(f.izquierda)
        + " "
        + simbolos[f.tipo]
        + " "
        + imprimir_formula(f.derecha)
        + ")"
    )


# ============================================================
# 2. CONSTRUCCION DEL ARBOL SEMANTICO
# ============================================================

@dataclass
class Entrada:
    formula: Formula
    verdad: bool
    aplicada: bool = False


@dataclass
class Rama:
    entradas: list = field(default_factory=list)
    estado: str = "abierta"
    motivo: str = ""


def atomos_opuestos(rama):
    """Detecta contradicciones entre atomos y sus negaciones."""

    vistos = {}

    for entrada in rama.entradas:
        f = entrada.formula

        if f.tipo == "atom":
            nombre = f.nombre
            valor = entrada.verdad

        elif f.tipo == "not" and f.izquierda.tipo == "atom":
            nombre = f.izquierda.nombre
            valor = not entrada.verdad

        else:
            continue

        if nombre in vistos and vistos[nombre] != valor:
            return True, f"Contradiccion: {nombre} y ¬{nombre}"

        vistos[nombre] = valor

    return False, ""


def expandir_entrada(entrada):
    """
    Aplica las reglas del tableau semantico.

    Cada elemento de la lista representa una alternativa.
    Las alternativas diferentes generan ramas diferentes.
    """

    f = entrada.formula
    v = entrada.verdad

    if f.tipo == "atom":
        return None

    # Negacion
    if f.tipo == "not":
        return [[(f.izquierda, not v)]]

    # Conjuncion
    if f.tipo == "and":
        if v:
            return [[
                (f.izquierda, True),
                (f.derecha, True)
            ]]

        return [
            [(f.izquierda, False)],
            [(f.derecha, False)]
        ]

    # Disyuncion
    if f.tipo == "or":
        if v:
            return [
                [(f.izquierda, True)],
                [(f.derecha, True)]
            ]

        return [[
            (f.izquierda, False),
            (f.derecha, False)
        ]]

    # Implicacion
    if f.tipo == "implica":
        if v:
            return [
                [(f.izquierda, False)],
                [(f.derecha, True)]
            ]

        return [[
            (f.izquierda, True),
            (f.derecha, False)
        ]]

    # Bicondicional
    if f.tipo == "bicond":
        if v:
            return [
                [
                    (f.izquierda, True),
                    (f.derecha, True)
                ],
                [
                    (f.izquierda, False),
                    (f.derecha, False)
                ]
            ]

        return [
            [
                (f.izquierda, True),
                (f.derecha, False)
            ],
            [
                (f.izquierda, False),
                (f.derecha, True)
            ]
        ]

    return None


def construir_arbol(formulas):
    """Construye las ramas hasta que se cierran o quedan abiertas."""

    ramas = [
        Rama([Entrada(f, True) for f in formulas])
    ]

    max_pasos = 300

    for _ in range(max_pasos):
        cambio = False
        nuevas_ramas = []

        for rama in ramas:

            if rama.estado == "cerrada":
                nuevas_ramas.append(rama)
                continue

            cerrada, motivo = atomos_opuestos(rama)

            if cerrada:
                rama.estado = "cerrada"
                rama.motivo = motivo
                nuevas_ramas.append(rama)
                continue

            indice = next(
                (
                    i for i, e in enumerate(rama.entradas)
                    if not e.aplicada and e.formula.tipo != "atom"
                ),
                None
            )

            if indice is None:
                rama.estado = "abierta"
                nuevas_ramas.append(rama)
                continue

            cambio = True

            entrada = rama.entradas[indice]
            entrada.aplicada = True

            alternativas = expandir_entrada(entrada)

            if not alternativas:
                nuevas_ramas.append(rama)
                continue

            for alternativa in alternativas:

                nueva = Rama(
                    entradas=[
                        Entrada(e.formula, e.verdad, e.aplicada)
                        for e in rama.entradas
                    ]
                )

                for formula, valor in alternativa:
                    nueva.entradas.append(
                        Entrada(formula, valor)
                    )

                cerrada, motivo = atomos_opuestos(nueva)

                if cerrada:
                    nueva.estado = "cerrada"
                    nueva.motivo = motivo

                nuevas_ramas.append(nueva)

        ramas = nuevas_ramas

        if not cambio:
            break

    return ramas


# ============================================================
# 3. DIBUJO DEL ARBOL SEMANTICO
# ============================================================

def dibujar_arbol(enlace_figura, contenedor, ramas):
    """Dibuja el arbol directamente dentro de la ventana."""

    for widget in contenedor.winfo_children():
        widget.destroy()

    cantidad = max(1, len(ramas))

    # Ajustar el ancho cuando hay muchas ramas
    ancho = max(10, cantidad * 2.5)

    fig = plt.Figure(figsize=(ancho, 7), dpi=100)
    ax = fig.add_subplot(111)

    ax.axis("off")
    ax.set_title(
        "ARBOL SEMANTICO",
        fontsize=16,
        fontweight="bold",
        pad=18
    )

    raiz_x = (cantidad - 1) / 2
    raiz_y = 0

    ax.text(
        raiz_x,
        raiz_y,
        "PREMISAS",
        ha="center",
        va="center",
        bbox=dict(
            boxstyle="round,pad=0.5",
            fc="#dceaf7",
            ec="#355c7d",
            lw=1.5
        ),
        fontsize=10,
        fontweight="bold"
    )

    max_nivel = 1

    for idx, rama in enumerate(ramas):
        x = idx

        # Evitar repetir exactamente la misma formula en la rama
        entradas = []
        vistos = set()

        for e in rama.entradas:
            texto = (
                ("T " if e.verdad else "F ")
                + imprimir_formula(e.formula)
            )

            if texto not in vistos:
                vistos.add(texto)
                entradas.append(texto)

        previo_x = raiz_x
        previo_y = raiz_y

        for j, texto in enumerate(entradas):
            nivel = j + 1
            y = -nivel
            max_nivel = max(max_nivel, nivel + 1)

            ax.plot(
                [previo_x, x],
                [previo_y - 0.12, y + 0.12],
                color="#657786",
                linewidth=1.2
            )

            ax.text(
                x,
                y,
                texto,
                ha="center",
                va="center",
                bbox=dict(
                    boxstyle="round,pad=0.35",
                    fc="#f4f6f8",
                    ec="#8a969f"
                ),
                fontsize=8
            )

            previo_x = x
            previo_y = y

        y_final = -(len(entradas) + 1)

        if rama.estado == "cerrada":
            color = "#f8d7da"
            borde = "#b02a37"
            etiqueta = "CERRADA X"
        else:
            color = "#d4edda"
            borde = "#198754"
            etiqueta = "ABIERTA"

        ax.plot(
            [previo_x, x],
            [previo_y - 0.12, y_final + 0.12],
            color=borde,
            linewidth=1.5
        )

        ax.text(
            x,
            y_final,
            etiqueta,
            ha="center",
            va="center",
            bbox=dict(
                boxstyle="round,pad=0.45",
                fc=color,
                ec=borde,
                lw=1.5
            ),
            fontsize=9,
            fontweight="bold"
        )

        max_nivel = max(max_nivel, len(entradas) + 2)

    ax.set_xlim(-1, max(1, cantidad))
    ax.set_ylim(-(max_nivel + 0.5), 0.8)

    fig.tight_layout()

    canvas = FigureCanvasTkAgg(fig, master=contenedor)
    canvas.draw()

    canvas.get_tk_widget().pack(
        fill="both",
        expand=True
    )

    enlace_figura["canvas"] = canvas
    enlace_figura["figura"] = fig


# ============================================================
# 4. INTERFAZ GRAFICA
# ============================================================

def analizar():
    texto = entrada_premisas.get("1.0", tk.END).strip()

    if not texto:
        messagebox.showwarning(
            "Faltan premisas",
            "Escribe una premisa por linea."
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
            "Error al interpretar",
            f"No pude interpretar una premisa:\n{error}"
        )
        return

    ramas = construir_arbol(formulas)

    abiertas = sum(
        rama.estado == "abierta"
        for rama in ramas
    )

    cerradas = sum(
        rama.estado == "cerrada"
        for rama in ramas
    )

    salida.delete("1.0", tk.END)

    salida.insert(
        tk.END,
        "PREMISAS INTERPRETADAS\n"
    )

    for i, formula in enumerate(formulas, start=1):
        salida.insert(
            tk.END,
            f"{i}. {imprimir_formula(formula)}\n"
        )

    salida.insert(
        tk.END,
        "\nRESULTADO DEL ARBOL SEMANTICO\n"
    )

    salida.insert(
        tk.END,
        f"Ramas abiertas: {abiertas}\n"
    )

    salida.insert(
        tk.END,
        f"Ramas cerradas: {cerradas}\n"
    )

    if abiertas:
        salida.insert(
            tk.END,
            "Conclusion: las premisas son CONSISTENTES.\n"
        )

        salida.insert(
            tk.END,
            "Existe al menos una rama abierta.\n"
        )

    else:
        salida.insert(
            tk.END,
            "Conclusion: las premisas son INCONSISTENTES.\n"
        )

        salida.insert(
            tk.END,
            "Todas las ramas se cerraron por contradiccion.\n"
        )

    # Dibujar el arbol automaticamente en la misma ventana
    dibujar_arbol(
        figura_actual,
        marco_arbol,
        ramas
    )


# ============================================================
# 5. CREAR VENTANA
# ============================================================

ventana = tk.Tk()

ventana.title("Logica I - Arbol semantico")
ventana.geometry("1200x850")
ventana.minsize(900, 650)

titulo = tk.Label(
    ventana,
    text="ARBOL SEMANTICO DE LOGICA PROPOSICIONAL",
    font=("Arial", 16, "bold")
)

titulo.pack(pady=(10, 4))

instrucciones = tk.Label(
    ventana,
    text=(
        "Escribe una premisa por linea. "
        "Ejemplo: Si es de dia, entonces voy a trabajar"
    ),
    font=("Arial", 10)
)

instrucciones.pack(pady=(0, 5))

entrada_premisas = scrolledtext.ScrolledText(
    ventana,
    height=5,
    font=("Arial", 11),
    wrap=tk.WORD
)

entrada_premisas.pack(
    fill="x",
    padx=12,
    pady=4
)

# Ejemplo inicial
entrada_premisas.insert(
    tk.END,
    "Si es de dia, entonces voy a trabajar\n"
    "Si llueve, entonces no voy a trabajar\n"
    "Es de dia"
)

boton = tk.Button(
    ventana,
    text="Analizar y mostrar arbol",
    command=analizar,
    font=("Arial", 11, "bold"),
    bg="#dceaf7",
    padx=12,
    pady=5
)

boton.pack(pady=6)

salida = scrolledtext.ScrolledText(
    ventana,
    height=7,
    font=("Consolas", 10),
    wrap=tk.WORD
)

salida.pack(
    fill="x",
    padx=12,
    pady=4
)

marco_arbol = tk.Frame(
    ventana,
    bd=1,
    relief="sunken"
)

marco_arbol.pack(
    fill="both",
    expand=True,
    padx=12,
    pady=(4, 12)
)

figura_actual = {}

# Analizar el ejemplo automaticamente al abrir
ventana.after(300, analizar)

ventana.mainloop()
