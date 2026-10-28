import re
import os
import json
import tkinter as tk
from tkinter import messagebox, scrolledtext, simpledialog
import unicodedata
from dataclasses import dataclass, field

import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

ARCHIVO_ESCENARIOS = "escenarios.json"

# ============================================================
# 1. UTILIDADES Y PERSISTENCIA
# ============================================================

def normalizar(texto):
    texto = texto.lower().strip()
    return "".join(
        c for c in unicodedata.normalize("NFD", texto)
        if unicodedata.category(c) != "Mn"
    )

def quitar_bordes(texto):
    texto = texto.strip()
    while texto.startswith("(") and texto.endswith(")"):
        nivel = 0
        valido = True
        for i, c in enumerate(texto):
            if c == "(": nivel += 1
            elif c == ")": nivel -= 1
            if nivel == 0 and i < len(texto) - 1:
                valido = False
                break
        if not valido: break
        texto = texto[1:-1].strip()
    return texto

def dividir(texto, patrones):
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
                    longitud = coincidencia.end()
                    izquierda = texto[:i]
                    derecha = texto[i + longitud:]
                    if izquierda.strip() and derecha.strip():
                        return izquierda.strip(), derecha.strip()
        i += 1
    return None

def cargar_datos_escenarios():
    if os.path.exists(ARCHIVO_ESCENARIOS):
        try:
            with open(ARCHIVO_ESCENARIOS, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}
    return {}

def guardar_datos_escenarios(datos):
    with open(ARCHIVO_ESCENARIOS, "w", encoding="utf-8") as f:
        json.dump(datos, f, ensure_ascii=False, indent=4)


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
    texto = quitar_bordes(texto.strip().rstrip(".;"))
    if not texto: raise ValueError("Se encontro una proposicion vacia.")
    norm = normalizar(texto)

    m = re.match(r"^\s*si\s+(.+?),?\s+entonces\s+(.+)\s*$", norm)
    if m:
        a, b = m.span(1), m.span(2)
        return Formula("implica", parsear(texto[a[0]:a[1]]), parsear(texto[b[0]:b[1]]))

    partes = dividir(texto, [r"\s+si y solo si\s+", r"\s+sii\s+", r"\s+↔\s+"])
    if partes: return Formula("bicond", parsear(partes[0]), parsear(partes[1]))

    partes = dividir(texto, [r"\s+implica\s+", r"\s+→\s+"])
    if partes: return Formula("implica", parsear(partes[0]), parsear(partes[1]))

    partes = dividir(texto, [r"\s+o\s+", r"\s+u\s+", r"\s+∨\s+"])
    if partes: return Formula("or", parsear(partes[0]), parsear(partes[1]))

    partes = dividir(texto, [r"\s+y\s+", r"\s+pero\s+", r"\s+aunque\s+", r"\s+∧\s+"])
    if partes: return Formula("and", parsear(partes[0]), parsear(partes[1]))

    if norm.startswith("no "): return Formula("not", izquierda=parsear(texto[3:]))
    prefijo = "es falso que "
    if norm.startswith(prefijo): return Formula("not", izquierda=parsear(texto[len(prefijo):]))
    if texto.startswith("¬"): return Formula("not", izquierda=parsear(texto[1:]))

    return Formula("atom", nombre=normalizar(texto), original=texto.strip())

def recoger_atomos(formula, resultado):
    if formula.tipo == "atom":
        resultado.setdefault(formula.nombre, formula.original)
        return
    if formula.izquierda: recoger_atomos(formula.izquierda, resultado)
    if formula.derecha is not None: recoger_atomos(formula.derecha, resultado)

def imprimir_formula(formula, simbolos):
    if formula.tipo == "atom":
        return simbolos[formula.nombre]
    if formula.tipo == "not":
        hijo = formula.izquierda
        texto = imprimir_formula(hijo, simbolos)
        if hijo.tipo == "atom" or hijo.tipo == "not":
            return "¬" + texto
        return "¬(" + texto + ")"
    operadores = {"and": "∧", "or": "∨", "implica": "→", "bicond": "↔"}
    a = imprimir_formula(formula.izquierda, simbolos)
    b = imprimir_formula(formula.derecha, simbolos)
    return f"({a} {operadores[formula.tipo]} {b})"


# ============================================================
# 3. TABLEAU SEMANTICO
# ============================================================

@dataclass
class Rama:
    entradas: list = field(default_factory=list)
    aplicadas: set = field(default_factory=set)
    estado: str = "abierta"
    motivo: str = ""

def clave(formula, verdad): return formula, verdad

def agregar(rama, formula, verdad):
    elemento = clave(formula, verdad)
    if elemento not in rama.entradas:
        rama.entradas.append(elemento)

def comprobar_contradiccion(rama):
    valores = {}
    for formula, verdad in rama.entradas:
        if formula.tipo == "atom":
            nombre = formula.nombre
            valor = verdad
        elif (formula.tipo == "not" and formula.izquierda.tipo == "atom"):
            nombre = formula.izquierda.nombre
            valor = not verdad
        else:
            continue
            
        if nombre in valores and valores[nombre] != valor:
            return True, f"{nombre} y ¬{nombre}"
        valores[nombre] = valor
    return False, ""

def es_alfa(formula, verdad):
    tipo = formula.tipo
    if tipo == "not": return True
    if tipo == "and" and verdad: return True
    if tipo == "and" and not verdad: return False
    if tipo == "or" and not verdad: return True
    if tipo == "or" and verdad: return False
    if tipo == "implica" and not verdad: return True
    if tipo == "implica" and verdad: return False
    if tipo == "bicond": return False
    return False

def expandir(formula, verdad):
    tipo, a, b = formula.tipo, formula.izquierda, formula.derecha
    if tipo == "atom": return None
    if tipo == "not" and a.tipo == "atom": return None 
    if tipo == "not": return [[(a, not verdad)]]
    
    if tipo == "and":
        if verdad: return [[(a, True), (b, True)]]
        return [[(a, False)], [(b, False)]]
    if tipo == "or":
        if verdad: return [[(a, True)], [(b, True)]]
        return [[(a, False), (b, False)]]
    if tipo == "implica":
        if verdad: return [[(a, False)], [(b, True)]]
        return [[(a, True), (b, False)]]
    if tipo == "bicond":
        if verdad: return [[(a, True), (b, True)], [(a, False), (b, False)]]
        return [[(a, True), (b, False)], [(a, False), (b, True)]]
    return None

def construir_arbol(formulas):
    ramas = [Rama()]
    for formula_premisa in formulas:
        for rama in ramas:
            if rama.estado == "abierta":
                agregar(rama, formula_premisa, True)
        
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
                rama.estado, rama.motivo = "cerrada", motivo
                nuevas.append(rama)
                continue
            
            pendientes = []
            for elemento in rama.entradas:
                f, v = elemento
                if f.tipo == "atom": continue
                if f.tipo == "not" and f.izquierda.tipo == "atom": continue
                if elemento not in rama.aplicadas:
                    pendientes.append(elemento)
            
            if not pendientes:
                nuevas.append(rama)
                continue
            
            cambio = True
            pendientes.sort(key=lambda x: not es_alfa(x[0], x[1]))
            pendiente = pendientes[0] 
            
            f, v = pendiente
            alternativas = expandir(f, v)
            rama.aplicadas.add(pendiente)
            
            if alternativas is None:
                nuevas.append(rama)
                continue
            
            for alternativa in alternativas:
                nueva = Rama(entradas=list(rama.entradas), aplicadas=set(rama.aplicadas))
                for f_alt, v_alt in alternativa: 
                    agregar(nueva, f_alt, v_alt)
                cerrada, motivo = comprobar_contradiccion(nueva)
                if cerrada: 
                    nueva.estado, nueva.motivo = "cerrada", motivo
                nuevas.append(nueva)
                
        ramas = nuevas
        if not cambio: 
            break 
            
    return ramas


# ============================================================
# 4. DIBUJAR EL ARBOL (Estilo Agrupado + Ajuste Altura)
# ============================================================

class NodoGrafico:
    def __init__(self, texto, es_raiz=False):
        self.texto = texto
        self.hijos = []
        self.x = 0
        self.y = 0
        self.estado = None
        self.motivo = ""
        self.es_raiz = es_raiz

def dibujar_arbol(contenedor, ramas, simbolos, formulas_premisas):
    for widget in contenedor.winfo_children(): widget.destroy()
    
    texto_raiz = ""
    for i, f in enumerate(formulas_premisas, 1):
        texto_raiz += f"({i}) {imprimir_formula(f, simbolos)}\n"
    
    raiz = NodoGrafico(texto_raiz.strip(), es_raiz=True)
    contador_pasos = len(formulas_premisas) + 1

    for rama in ramas:
        actual = raiz
        pasos_rama = rama.entradas[len(formulas_premisas):] 
        
        for formula, verdad in pasos_rama:
            texto = f"({contador_pasos}) " + ("" if verdad else "¬") + imprimir_formula(formula, simbolos)
            siguiente = next((h for h in actual.hijos if texto in h.texto), None)
            if not siguiente:
                siguiente = NodoGrafico(texto)
                actual.hijos.append(siguiente)
                contador_pasos += 1
            actual = siguiente
            
        actual.estado = rama.estado
        actual.motivo = rama.motivo

    min_y = 0 

    def asignar_posiciones(nodo, nivel=0, x_hoja=0):
        nonlocal min_y
        nodo.y = -nivel * 1.5
        min_y = min(min_y, nodo.y)
        if not nodo.hijos:
            nodo.x = x_hoja
            return x_hoja + 1
        siguiente_x = x_hoja
        x_hijos = []
        for hijo in nodo.hijos:
            siguiente_x = asignar_posiciones(hijo, nivel + 1, siguiente_x)
            x_hijos.append(hijo.x)
        nodo.x = sum(x_hijos) / len(x_hijos)
        return siguiente_x

    total_hojas = asignar_posiciones(raiz)
    
    ancho = max(8, total_hojas * 3)
    alto = max(5, abs(min_y) + 2.5) 
    
    figura = plt.Figure(figsize=(ancho, alto), dpi=100)
    ax = figura.add_subplot(111)
    ax.axis("off")
    
    def dibujar_nodo(nodo, x_padre=None, y_padre=None):
        if x_padre is not None and y_padre is not None:
            ax.plot([x_padre, nodo.x], [y_padre - 0.35, nodo.y + 0.3], color="black", linewidth=1)
        
        ax.text(nodo.x, nodo.y, nodo.texto, ha="center", va="center", fontsize=9, 
                bbox=dict(boxstyle="square,pad=0.5", fc="#f8f9fa", ec="black"))
        
        if not nodo.hijos:
            y_final = nodo.y - 0.8
            if nodo.estado == "cerrada":
                txt_cierre = f"X CERRADA\n({nodo.motivo})" if nodo.motivo else "X CERRADA"
                ax.text(nodo.x, y_final, txt_cierre, ha="center", va="center", fontsize=8, color="darkred",
                        fontweight="bold", bbox=dict(boxstyle="square,pad=0.4", fc="#f8d7da", ec="#b02a37"))
            elif nodo.estado == "abierta":
                ax.text(nodo.x, y_final, "O ABIERTA", ha="center", va="center", fontsize=8, color="darkgreen",
                        fontweight="bold", bbox=dict(boxstyle="square,pad=0.4", fc="#d4edda", ec="#198754"))
        
        for hijo in nodo.hijos:
            dibujar_nodo(hijo, nodo.x, nodo.y)

    dibujar_nodo(raiz)
    ax.set_xlim(-0.5, total_hojas - 0.5)
    ax.set_ylim(min_y - 1.5, 1.0) 
    figura.tight_layout()
    
    canvas = FigureCanvasTkAgg(figura, master=contenedor)
    canvas.draw()
    canvas.get_tk_widget().pack(fill="both", expand=True)
    return figura


# ============================================================
# 5. ANALIZAR PREMISAS Y GESTION DE ESCENARIOS
# ============================================================

def analizar():
    texto = entrada.get("1.0", tk.END).strip()
    if not texto:
        messagebox.showwarning("Aviso", "Escribe al menos una premisa.")
        return
    lineas = [linea.strip() for linea in texto.splitlines() if linea.strip()]
    try:
        formulas = [parsear(linea) for linea in lineas]
    except Exception as error:
        messagebox.showerror("Error de interpretacion", str(error))
        return

    atomos = {}
    for formula in formulas: recoger_atomos(formula, atomos)

    letras = "pqrstuvwxyzabcdefghijklmno"
    simbolos = {nombre: letras[i] if i < len(letras) else f"p{i+1}" for i, nombre in enumerate(atomos)}

    ramas = construir_arbol(formulas)
    abiertas = sum(r.estado == "abierta" for r in ramas)
    cerradas = sum(r.estado == "cerrada" for r in ramas)

    # TEXTO FORMATEADO COMO EN LA IMAGEN DEL PROFESOR
    str_atomos = " | ".join([f'{simbolos[n]} = «{orig}»' for n, orig in atomos.items()])
    str_formulas = " | ".join([f'R{i+1}: {imprimir_formula(f, simbolos)}' for i, f in enumerate(formulas)])
    
    # Extraer los modelos verdaderos para las ramas abiertas
    modelos_str = []
    if abiertas > 0:
        for i, rama in enumerate([r for r in ramas if r.estado == "abierta"], 1):
            asig_unicas = dict()
            for f, v in rama.entradas:
                if f.tipo == "atom": 
                    asig_unicas[simbolos[f.nombre]] = "V" if v else "F"
                elif f.tipo == "not" and f.izquierda.tipo == "atom": 
                    asig_unicas[simbolos[f.izquierda.nombre]] = "F" if v else "V"
            str_asig = ", ".join([f"{k} = {v}" for k, v in sorted(asig_unicas.items())])
            modelos_str.append(f"Modelo {i}: {{{str_asig}}}")
        str_conclusion = "CONSISTENTE -> " + " ; ".join(modelos_str)
    else:
        str_conclusion = "INCONSISTENTE (Todas las ramas cerraron)"

    salida.delete("1.0", tk.END)
    salida.insert(tk.END, "ESCENARIO ACTIVO\n")
    salida.insert(tk.END, f"TABLA DE ÁTOMOS : {str_atomos}\n")
    salida.insert(tk.END, f"FÓRMULAS LÓGICAS: {str_formulas}\n")
    salida.insert(tk.END, f"RAMAS DEL ÁRBOL : {cerradas} cerrada(s) (X) y {abiertas} abierta(s) (O)\n")
    salida.insert(tk.END, f"CONCLUSIÓN      : {str_conclusion}\n")

    dibujar_arbol(marco_arbol, ramas, simbolos, formulas)


def guardar_escenario():
    texto = entrada.get("1.0", tk.END).strip()
    if not texto:
        messagebox.showwarning("Aviso", "No hay premisas para guardar.")
        return
    nombre = simpledialog.askstring("Guardar", "Nombre del escenario:", parent=ventana)
    if nombre and nombre.strip():
        datos = cargar_datos_escenarios()
        datos[nombre.strip()] = texto
        guardar_datos_escenarios(datos)
        messagebox.showinfo("Éxito", f"Escenario '{nombre}' guardado correctamente.")

def cargar_escenario():
    datos = cargar_datos_escenarios()
    if not datos:
        messagebox.showinfo("Aviso", "No hay escenarios guardados aún.")
        return

    vent_cargar = tk.Toplevel(ventana)
    vent_cargar.title("Cargar Escenario")
    vent_cargar.geometry("300x250")
    vent_cargar.transient(ventana) 
    vent_cargar.grab_set()         

    tk.Label(vent_cargar, text="Selecciona un escenario:", font=("Arial", 11)).pack(pady=5)
    lista = tk.Listbox(vent_cargar, font=("Arial", 10))
    lista.pack(fill="both", expand=True, padx=10, pady=5)

    for nombre in datos.keys():
        lista.insert(tk.END, nombre)

    def seleccionar():
        seleccion = lista.curselection()
        if seleccion:
            nombre = lista.get(seleccion[0])
            entrada.delete("1.0", tk.END)
            entrada.insert(tk.END, datos[nombre])
            vent_cargar.destroy()
            analizar() 
        else:
            messagebox.showwarning("Aviso", "Selecciona un escenario.", parent=vent_cargar)

    tk.Button(vent_cargar, text="Cargar seleccionado", command=seleccionar, font=("Arial", 10, "bold"), bg="#dceaf7").pack(pady=10)


# ============================================================
# 6. INTERFAZ GRAFICA
# ============================================================

ventana = tk.Tk()
ventana.title("Logica I - Arbol semantico")
ventana.geometry("1200x850")
ventana.minsize(850, 600)

tk.Label(ventana, text="ARBOL SEMANTICO DE LOGICA PROPOSICIONAL", font=("Arial", 15, "bold")).pack(pady=8)
tk.Label(ventana, text="Escribe una premisa por linea. Usa conectores como y, o, no, implica, si... entonces, si y solo si.", wraplength=1000).pack()

entrada = scrolledtext.ScrolledText(ventana, height=5, font=("Arial", 11), wrap=tk.WORD)
entrada.pack(fill="x", padx=12, pady=6)
entrada.insert(tk.END, "Estudio o trabajo\nsi estudio entonces apruebo o pido asesoria\nno trabajo")

marco_botones = tk.Frame(ventana)
marco_botones.pack(pady=4)

tk.Button(marco_botones, text="Analizar y mostrar arbol", command=analizar, font=("Arial", 11, "bold"), bg="#dceaf7", padx=12, pady=5).pack(side=tk.LEFT, padx=5)
tk.Button(marco_botones, text="Guardar escenario", command=guardar_escenario, font=("Arial", 10), bg="#e2f0cb", padx=12, pady=5).pack(side=tk.LEFT, padx=5)
tk.Button(marco_botones, text="Cargar escenario", command=cargar_escenario, font=("Arial", 10), bg="#ffdfba", padx=12, pady=5).pack(side=tk.LEFT, padx=5)

# TEXT AREA reducida para el nuevo formato compacto
salida = scrolledtext.ScrolledText(ventana, height=5, font=("Consolas", 10), wrap=tk.WORD, bg="#f4f4f4")
salida.pack(fill="x", padx=12, pady=5)

marco_arbol = tk.Frame(ventana, bd=1, relief="sunken", bg="white")
marco_arbol.pack(fill="both", expand=True, padx=12, pady=(2, 10))

ventana.after(300, analizar)
ventana.mainloop()