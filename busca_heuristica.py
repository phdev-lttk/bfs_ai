"""
BUSCA HEURÍSTICA (GREEDY BEST-FIRST SEARCH)
Base de Atendimento  ->  Hospital Central

Como funciona (resumo para a apresentação):
  - A "fronteira" é a lista de estados DISPONÍVEIS (descobertos e ainda não expandidos).
  - A cada passo, escolhemos na fronteira INTEIRA o estado com MENOR h(n)
    (não só entre os vizinhos do último estado expandido).
  - Se for o objetivo, paramos e reconstruímos o caminho pelos predecessores.
  - Senão, expandimos: vizinhos ainda NÃO visitados entram na fronteira.

Definições usadas:
  - VISITADO  = estado que foi descoberto e entrou na fronteira (marcado para nunca entrar de novo).
  - EXPANDIDO = estado que saiu da fronteira e teve seus vizinhos examinados.
    (O objetivo é selecionado e reconhecido, mas não é expandido.)

CRITÉRIO DE DESEMPATE: se dois ou mais estados tiverem o mesmo h(n),
vence o que foi DESCOBERTO PRIMEIRO (menor ordem de inserção na fronteira).

HEURÍSTICA h(n): distância em linha reta aproximada (em km) até o Hospital,
medida sobre o mapa (POSICOES), com escala de 1 km = 30 pixels:
    h(n) = round( distância_em_pixels(n, Hospital) / 30 )
Estados mais próximos do hospital têm h menor. Aeroporto e Shopping ficam
perto do hospital em linha reta, mas não têm saída: são as "armadilhas".

Para conferir os valores e os requisitos do grafo:  python busca_heuristica.py --conferir
"""

import math
import sys
import tkinter as tk
from tkinter import scrolledtext

GRAFO = {
    "Base":         ["Centro", "Parque", "Rodoviária"],
    "Centro":       ["Shopping", "Universidade"],
    "Parque":       ["Terminal", "Universidade"],
    "Rodoviária":   ["Terminal", "Mercado"],
    "Mercado":      ["Terminal"],
    "Terminal":     ["Avenida"],
    "Universidade": ["Ponte", "Aeroporto"],
    "Avenida":      ["Hospital"],
    "Ponte":        ["Hospital"],
    "Shopping":     [],
    "Aeroporto":    [],
    "Hospital":     [],
}

INICIO = "Base"
OBJETIVO = "Hospital"
NOME_ORIGEM = "Base de Atendimento"
NOME_DESTINO = "Hospital Central"


ESCALA_PX_POR_KM = 30

# Heurística ORIGINAL: distância em linha reta até o Hospital (km)
H_ORIGINAL = {
    "Base": 18,
    "Centro": 10,
    "Rodoviária": 12,
    "Parque": 7,
    "Shopping": 6,
    "Terminal": 8,
    "Universidade": 5,
    "Ponte": 4,
    "Aeroporto": 3,
    "Mercado": 11,
    "Avenida": 4,
    "Hospital": 0,
}

ALTERACOES = {"Centro": 4, "Parque": 13, "Universidade": 11}
H_MODIFICADA = {**H_ORIGINAL, **ALTERACOES}


LARGURA, ALTURA, RAIO = 720, 490, 22

POSICOES = {
    "Base": (80, 240),
    "Centro": (350, 110),
    "Shopping": (580, 60),
    "Universidade": (500, 140),
    "Aeroporto": (610, 150),
    "Ponte": (500, 240),
    "Hospital": (620, 240),
    "Parque": (410, 270),
    "Terminal": (420, 360),
    "Avenida": (560, 350),
    "Rodoviária": (290, 360),
    "Mercado": (355, 435),
}

ROTULO = {
    "Base": (0, 34), "Centro": (0, -34), "Shopping": (0, 34),
    "Universidade": (0, -34), "Aeroporto": (0, 34), "Ponte": (0, 34),
    "Parque": (-10, -34), "Terminal": (30, 32), "Rodoviária": (-25, 32),
    "Mercado": (0, 34), "Avenida": (0, 34), "Hospital": (48, 0),
}

FONTE_MONO = ("Courier", 10)


def ponto_na_borda(p1, p2, raio):
    """Encurta a seta para ela começar/terminar na borda dos círculos."""
    dx, dy = p2[0] - p1[0], p2[1] - p1[1]
    d = math.hypot(dx, dy)
    ux, uy = dx / d, dy / d
    return (p1[0] + ux * raio, p1[1] + uy * raio), (p2[0] - ux * raio, p2[1] - uy * raio)


class BuscaHeuristica:
    def __init__(self, grafo, h, inicio, objetivo):
        self.grafo = grafo
        self.h = h
        self.inicio = inicio
        self.objetivo = objetivo
        self.reiniciar()

    def reiniciar(self):
        self.fronteira = [self.inicio]            # estados disponíveis
        self.visitados = {self.inicio}            # controle de visitados
        self.ordem_insercao = {self.inicio: 0}    # usada no desempate
        self.contador = 1
        self.predecessor = {self.inicio: None}    # para reconstruir o caminho
        self.ordem_visita = [self.inicio]
        self.ordem_expansao = []
        self.atual = None
        self.passo = 0
        self.finalizado = False
        self.encontrou = False
        self.caminho = []
        self.proximo, _ = self.selecionar_menor()

    def chave(self, estado):
        """Chave de comparação: menor h; em empate, quem foi descoberto primeiro."""
        return (self.h[estado], self.ordem_insercao[estado])

    def selecionar_menor(self):
        """Percorre TODA a fronteira e devolve (escolhido, lista_de_empatados)."""
        melhor = self.fronteira[0]
        for candidato in self.fronteira[1:]:
            if self.chave(candidato) < self.chave(melhor):
                melhor = candidato
        empatados = sorted(
            (e for e in self.fronteira if self.h[e] == self.h[melhor]),
            key=self.ordem_insercao.get,
        )
        return melhor, empatados

    def texto_fronteira(self):
        if not self.fronteira:
            return "(vazia)"
        ordenados = sorted(self.fronteira, key=self.chave)
        return ", ".join(f"{e} h={self.h[e]}" for e in ordenados)

    def texto_proximo(self):
        if self.proximo is None:
            return "-"
        _, empatados = self.selecionar_menor()
        txt = f"{self.proximo} (h={self.h[self.proximo]})"
        if len(empatados) > 1:
            txt += (f"  [empate entre {', '.join(empatados)}; "
                    f"desempate: descoberto primeiro]")
        return txt

    def reconstruir_caminho(self):
        caminho, estado = [], self.objetivo
        while estado is not None:
            caminho.append(estado)
            estado = self.predecessor[estado]
        return caminho[::-1]

    def proximo_passo(self):
        """Executa um passo da busca e devolve as linhas para exibir."""
        if self.finalizado:
            return []

        self.passo += 1
        estado, _ = self.selecionar_menor()
        self.fronteira.remove(estado)
        self.atual = estado
        linhas = [f"PASSO {self.passo}"]

        # --- é o objetivo? ---
        if estado == self.objetivo:
            self.finalizado = True
            self.encontrou = True
            self.proximo = None
            self.caminho = self.reconstruir_caminho()
            linhas.append(f"  Estado selecionado: {estado} (h={self.h[estado]})")
            linhas.append("  É o objetivo! Busca encerrada (objetivo não é expandido).")
            linhas.append("  Caminho (via predecessores): " + " -> ".join(self.caminho))
            return linhas

        # --- expandir ---
        self.ordem_expansao.append(estado)
        novos, ignorados = [], []
        for vizinho in self.grafo[estado]:
            if vizinho in self.visitados:
                ignorados.append(vizinho)
            else:
                self.visitados.add(vizinho)
                self.predecessor[vizinho] = estado
                self.ordem_insercao[vizinho] = self.contador
                self.contador += 1
                self.fronteira.append(vizinho)
                self.ordem_visita.append(vizinho)
                novos.append(vizinho)

        linhas.append(f"  Estado expandido: {estado} (h={self.h[estado]})")
        if not self.grafo[estado]:
            linhas.append("  Novos estados encontrados: nenhum (estado SEM SAÍDA)")
        elif novos:
            linhas.append("  Novos estados encontrados: "
                          + ", ".join(f"{v} h={self.h[v]}" for v in novos))
        else:
            linhas.append("  Novos estados encontrados: nenhum (vizinhos já visitados)")
        if ignorados and novos:
            linhas.append("  Já visitados (ignorados): " + ", ".join(ignorados))
        linhas.append(f"  Disponíveis: {self.texto_fronteira()}")

        if self.fronteira:
            self.proximo, _ = self.selecionar_menor()
            linhas.append(f"  Próximo escolhido: {self.texto_proximo()}")
        else:
            self.proximo = None
            self.finalizado = True
            linhas.append("  Não há mais estados disponíveis: objetivo NÃO encontrado.")
        return linhas

    def resultado(self):
        seta = " -> "
        linhas = [
            f"Origem: {self.inicio} ({NOME_ORIGEM})",
            f"Destino: {self.objetivo} ({NOME_DESTINO})",
            "Ordem de visita: " + seta.join(self.ordem_visita),
            "Ordem de expansão: " + seta.join(self.ordem_expansao),
        ]
        if self.encontrou:
            linhas.append("Caminho encontrado: " + seta.join(self.caminho)
                          + f" ({len(self.caminho) - 1} ligações)")
        else:
            linhas.append("Caminho encontrado: nenhum")
        linhas.append(f"Estados visitados: {len(self.ordem_visita)}")
        linhas.append(f"Estados expandidos: {len(self.ordem_expansao)}")
        return linhas


def executar_completa(h):
    busca = BuscaHeuristica(GRAFO, h, INICIO, OBJETIVO)
    while not busca.finalizado:
        busca.proximo_passo()
    return busca


def texto_comparacao(o, m):
    """Tabela comparativa entre a execução original (o) e a modificada (m)."""
    sim = lambda x: "Sim" if x else "Não"
    seta = " -> "
    so_o = [e for e in o.ordem_visita if e not in m.ordem_visita]
    so_m = [e for e in m.ordem_visita if e not in o.ordem_visita]
    alt = ", ".join(f"{k} {H_ORIGINAL[k]} -> {v}" for k, v in ALTERACOES.items())
    linhas = [
        f"Valores alterados: {alt}", "",
        "Caminho encontrado",
        "  Original:   " + seta.join(o.caminho),
        "  Modificada: " + seta.join(m.caminho), "",
        "Estados visitados",
        f"  Original:   {len(o.ordem_visita)}",
        f"  Modificada: {len(m.ordem_visita)}", "",
        "Estados expandidos",
        f"  Original:   {len(o.ordem_expansao)}",
        f"  Modificada: {len(m.ordem_expansao)}", "",
        "Ordem de visita",
        "  Original:   " + seta.join(o.ordem_visita),
        "  Modificada: " + seta.join(m.ordem_visita), "",
        "Ordem de expansão",
        "  Original:   " + seta.join(o.ordem_expansao),
        "  Modificada: " + seta.join(m.ordem_expansao), "",
        "-" * 60,
        f"A ordem de visita mudou?  {sim(o.ordem_visita != m.ordem_visita)}",
        f"O caminho mudou?          {sim(o.caminho != m.caminho)}",
        f"Visitados mudou?          {sim(len(o.ordem_visita) != len(m.ordem_visita))}"
        f" ({len(o.ordem_visita)} x {len(m.ordem_visita)})",
        f"Expandidos mudou?         {sim(len(o.ordem_expansao) != len(m.ordem_expansao))}"
        f" ({len(o.ordem_expansao)} x {len(m.ordem_expansao)})",
        "Visitados só na original:   " + (", ".join(so_o) or "nenhum"),
        "Visitados só na modificada: " + (", ".join(so_m) or "nenhum"),
    ]
    return "\n".join(linhas)


class AppBusca:
    def __init__(self, janela):
        self.janela = janela
        self.janela.title("Busca Heurística - Base de Atendimento -> Hospital Central")
        self.auto_id = None
        self.var_heuristica = tk.StringVar(value="original")

        self.canvas = tk.Canvas(janela, width=LARGURA, height=ALTURA, bg="white",
                                highlightthickness=1, highlightbackground="gray")
        self.canvas.grid(row=0, column=0, padx=(15, 5), pady=(15, 5))

        tk.Label(
            janela, justify="left", wraplength=LARGURA, font=("Arial", 9),
            text=("Número no círculo = h(n)  |  Amarelo = disponível (visitado, não expandido)  |  "
                  "Laranja = expandido agora  |  Cinza = já expandido  |  "
                  "Borda vermelha = próximo escolhido  |  Seta azul = descoberta do estado  |  "
                  "Seta verde = caminho final"),
        ).grid(row=1, column=0, sticky="w", padx=15)

        painel = tk.Frame(janela)
        painel.grid(row=0, column=1, rowspan=2, sticky="n", padx=10, pady=15)

        tk.Label(painel, text="Busca Heurística",
                 font=("Arial", 16, "bold")).pack(anchor="w")

        # escolha da heurística
        f_h = tk.Frame(painel)
        f_h.pack(anchor="w", pady=(6, 0))
        tk.Label(f_h, text="Heurística:", font=("Arial", 10, "bold")).pack(side="left")
        tk.Radiobutton(f_h, text="Original", variable=self.var_heuristica,
                       value="original", command=self.reiniciar).pack(side="left")
        tk.Radiobutton(f_h, text="Modificada", variable=self.var_heuristica,
                       value="modificada", command=self.reiniciar).pack(side="left")
        tk.Label(painel, font=("Arial", 9), fg="gray30", justify="left",
                 text="Desempate: mesmo h(n) -> vence o estado descoberto primeiro."
                 ).pack(anchor="w")

        # botões
        f_b = tk.Frame(painel)
        f_b.pack(anchor="w", pady=8)
        tk.Button(f_b, text="Próximo passo", width=13, font=("Arial", 10, "bold"),
                  command=self.proximo_passo).pack(side="left", padx=2)
        tk.Button(f_b, text="Executar tudo", width=12,
                  command=self.executar_tudo).pack(side="left", padx=2)
        tk.Button(f_b, text="Reiniciar", width=9,
                  command=self.reiniciar).pack(side="left", padx=2)
        tk.Button(f_b, text="Comparar", width=9,
                  command=self.comparar).pack(side="left", padx=2)

        self.lbl_passo = tk.Label(painel, text="Passo: 0", font=("Arial", 11, "bold"))
        self.lbl_passo.pack(anchor="w")

        tk.Label(painel, text="Estados disponíveis (menor h primeiro; ► = próximo):",
                 font=("Arial", 10, "bold")).pack(anchor="w", pady=(6, 0))
        self.txt_fronteira = tk.Text(painel, width=58, height=6, font=FONTE_MONO)
        self.txt_fronteira.pack(anchor="w")

        tk.Label(painel, text="Histórico da busca:",
                 font=("Arial", 10, "bold")).pack(anchor="w", pady=(6, 0))
        self.txt_log = scrolledtext.ScrolledText(painel, width=58, height=11,
                                                 font=FONTE_MONO, wrap="word")
        self.txt_log.pack(anchor="w")

        tk.Label(painel, text="Resultado final:",
                 font=("Arial", 10, "bold")).pack(anchor="w", pady=(6, 0))
        self.txt_resultado = tk.Text(painel, width=58, height=9,
                                     font=FONTE_MONO, wrap="word")
        self.txt_resultado.pack(anchor="w")

        self.reiniciar()

    def _definir_texto(self, widget, texto):
        widget.config(state="normal")
        widget.delete("1.0", tk.END)
        widget.insert(tk.END, texto)
        widget.config(state="disabled")

    def _acrescentar_log(self, linhas):
        self.txt_log.config(state="normal")
        self.txt_log.insert(tk.END, "\n".join(linhas) + "\n")
        self.txt_log.see(tk.END)
        self.txt_log.config(state="disabled")

    def heuristica_atual(self):
        return H_MODIFICADA if self.var_heuristica.get() == "modificada" else H_ORIGINAL

    def reiniciar(self):
        self.parar_auto()
        self.busca = BuscaHeuristica(GRAFO, self.heuristica_atual(), INICIO, OBJETIVO)
        b = self.busca
        self._definir_texto(self.txt_log, "")
        self._definir_texto(self.txt_resultado, "")
        self._acrescentar_log([
            f"HEURÍSTICA {self.var_heuristica.get().upper()}",
            f"INÍCIO: {b.texto_fronteira()}",
            f"  Próximo escolhido: {b.texto_proximo()}",
            "",
        ])
        self.atualizar()

    def proximo_passo(self):
        b = self.busca
        if b.finalizado:
            return
        self._acrescentar_log(b.proximo_passo() + [""])
        if b.finalizado:
            self._definir_texto(self.txt_resultado, "\n".join(b.resultado()))
        self.atualizar()

    def executar_tudo(self):
        self.parar_auto()
        self._passo_automatico()

    def _passo_automatico(self):
        if self.busca.finalizado:
            self.auto_id = None
            return
        self.proximo_passo()
        self.auto_id = self.janela.after(900, self._passo_automatico)

    def parar_auto(self):
        if self.auto_id is not None:
            self.janela.after_cancel(self.auto_id)
            self.auto_id = None

    def comparar(self):
        orig = executar_completa(H_ORIGINAL)
        mod = executar_completa(H_MODIFICADA)
        top = tk.Toplevel(self.janela)
        top.title("Comparação: heurística original x modificada")
        txt = scrolledtext.ScrolledText(top, width=95, height=32, font=FONTE_MONO, wrap="word")
        txt.pack(padx=10, pady=10)
        txt.insert(tk.END, texto_comparacao(orig, mod))
        txt.config(state="disabled")

    def atualizar(self):
        b = self.busca
        self.lbl_passo.config(text=f"Passo: {b.passo}")

        if b.fronteira:
            linhas = []
            for e in sorted(b.fronteira, key=b.chave):
                marca = "►" if e == b.proximo else " "
                linhas.append(f"{marca} {e:<14} h={b.h[e]}")
            texto = "\n".join(linhas)
        else:
            texto = "(fronteira vazia)"
        self._definir_texto(self.txt_fronteira, texto)
        self.desenhar()

    def cor_do_no(self, no):
        b = self.busca
        if b.encontrou and no in b.caminho:
            return "lightgreen"
        if no == b.atual:
            return "orange"
        if no in b.ordem_expansao:
            return "lightgray"
        if no in b.fronteira:
            return "gold"
        return "white"

    def texto_com_fundo(self, x, y, texto, fonte, cor):
        t = self.canvas.create_text(x, y, text=texto, font=fonte, fill=cor)
        fundo = self.canvas.create_rectangle(self.canvas.bbox(t), fill="white", outline="")
        self.canvas.tag_lower(fundo, t)

    def desenhar(self):
        b = self.busca
        c = self.canvas
        c.delete("all")
        arestas_caminho = set(zip(b.caminho, b.caminho[1:])) if b.encontrou else set()

        for origem, destinos in GRAFO.items():
            for destino in destinos:
                p1, p2 = ponto_na_borda(POSICOES[origem], POSICOES[destino], RAIO)
                if (origem, destino) in arestas_caminho:
                    cor, larg = "green4", 5
                elif b.predecessor.get(destino) == origem:
                    cor, larg = "royalblue", 3
                else:
                    cor, larg = "gray60", 2
                c.create_line(*p1, *p2, width=larg, fill=cor,
                              arrow=tk.LAST, arrowshape=(12, 14, 5))

        for no, (x, y) in POSICOES.items():
            borda, larg = ("red", 4) if no == b.proximo else ("black", 2)
            c.create_oval(x - RAIO, y - RAIO, x + RAIO, y + RAIO,
                          fill=self.cor_do_no(no), outline=borda, width=larg)
            c.create_text(x, y, text=f"h={b.h[no]}", font=("Arial", 10, "bold"))

            dx, dy = ROTULO[no]
            self.texto_com_fundo(x + dx, y + dy, no, ("Arial", 10, "bold"), "black")
            if no == INICIO:
                extra = ("INÍCIO", "blue")
            elif no == OBJETIVO:
                extra = ("OBJETIVO", "green4")
            elif not GRAFO[no]:
                extra = ("sem saída", "red")
            else:
                extra = None
            if extra:
                self.texto_com_fundo(x + dx, y + dy + 14, extra[0], ("Arial", 8, "bold"), extra[1])

def todos_os_caminhos(atual=INICIO, percorrido=None):
    percorrido = (percorrido or []) + [atual]
    if atual == OBJETIVO:
        return [percorrido]
    achados = []
    for v in GRAFO[atual]:
        if v not in percorrido:
            achados += todos_os_caminhos(v, percorrido)
    return achados


def conferir():
    print("h(n) da tabela x h(n) calculado pelas posições do mapa (escala 30 px = 1 km)")
    for no in GRAFO:
        dist = math.dist(POSICOES[no], POSICOES[OBJETIVO])
        print(f"  {no:<13} tabela={H_ORIGINAL[no]:>2}  distância={dist / ESCALA_PX_POR_KM:5.2f} km")
    caminhos = todos_os_caminhos()
    print(f"\nEstados: {len(GRAFO)} (mín. 10)")
    print(f"Conexões: {sum(len(v) for v in GRAFO.values())} (mín. 14)")
    print(f"Caminhos entre origem e objetivo: {len(caminhos)} (mín. 3)")
    for cam in caminhos:
        print("   ", " -> ".join(cam))
    print("Estados sem saída:", [n for n, v in GRAFO.items() if not v and n != OBJETIVO])
    print("h definido para todos:", set(GRAFO) == set(H_ORIGINAL) == set(H_MODIFICADA))
    print("h(objetivo) = 0:", H_ORIGINAL[OBJETIVO] == 0 and H_MODIFICADA[OBJETIVO] == 0)


if __name__ == "__main__":
    if "--conferir" in sys.argv:
        conferir()
    else:
        raiz = tk.Tk()
        AppBusca(raiz)
        raiz.mainloop()
