#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Ứng dụng Trực Quan Hóa và Phân Tích Đồ Thị
Graph Visualization & Analysis Application
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import networkx as nx
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
from collections import deque, defaultdict
import json
from typing import List, Dict, Set, Tuple, Optional
import pickle


# ============ LỚP ĐỒNG THỊ =============
class Graph:
    """Lớp đại diện cho đồ thị"""
    
    def __init__(self, is_directed=False):
        self.is_directed = is_directed
        self.adjacency_list = defaultdict(list)
        self.vertices = set()
        self.edge_list = []
        
    def add_edge(self, u, v, weight=1):
        """Thêm cạnh vào đồ thị"""
        self.vertices.add(u)
        self.vertices.add(v)
        self.adjacency_list[u].append((v, weight))
        if not self.is_directed:
            self.adjacency_list[v].append((u, weight))
        self.edge_list.append((u, v, weight))
        
    def add_vertex(self, v):
        """Thêm đỉnh"""
        self.vertices.add(v)
        if v not in self.adjacency_list:
            self.adjacency_list[v] = []
    
    def to_adjacency_matrix(self):
        """Chuyển đồ thị sang ma trận kề"""
        vertices_list = sorted(list(self.vertices))
        n = len(vertices_list)
        matrix = [[0] * n for _ in range(n)]
        vertex_to_idx = {v: i for i, v in enumerate(vertices_list)}
        
        for u in self.adjacency_list:
            for v, weight in self.adjacency_list[u]:
                i = vertex_to_idx[u]
                j = vertex_to_idx[v]
                matrix[i][j] = weight
                
        return matrix, vertices_list
    
    def from_adjacency_matrix(self, matrix, vertices_list):
        """Tạo đồ thị từ ma trận kề"""
        self.vertices = set(vertices_list)
        self.adjacency_list.clear()
        self.edge_list.clear()
        
        for u in vertices_list:
            self.adjacency_list[u] = []
        
        for i, u in enumerate(vertices_list):
            for j, v in enumerate(vertices_list):
                if matrix[i][j] != 0:
                    weight = matrix[i][j]
                    self.adjacency_list[u].append((v, weight))
                    if (u, v, weight) not in self.edge_list:
                        self.edge_list.append((u, v, weight))
    
    def to_edge_list(self):
        """Chuyển sang danh sách cạnh"""
        return self.edge_list.copy()
    
    def from_edge_list(self, edges):
        """Tạo đồ thị từ danh sách cạnh"""
        self.vertices.clear()
        self.adjacency_list.clear()
        self.edge_list = edges.copy()
        
        for u, v, weight in edges:
            self.add_edge(u, v, weight)
    
    def bfs(self, start):
        """Duyệt theo chiều rộng"""
        visited = set()
        queue = deque([start])
        visited.add(start)
        result = []
        
        while queue:
            vertex = queue.popleft()
            result.append(vertex)
            
            for neighbor, _ in self.adjacency_list[vertex]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append(neighbor)
        
        return result
    
    def dfs(self, start):
        """Duyệt theo chiều sâu"""
        visited = set()
        result = []
        
        def dfs_helper(v):
            visited.add(v)
            result.append(v)
            for neighbor, _ in self.adjacency_list[v]:
                if neighbor not in visited:
                    dfs_helper(neighbor)
        
        dfs_helper(start)
        return result
    
    def shortest_path_bfs(self, start, end):
        """Tìm đường đi ngắn nhất sử dụng BFS"""
        if start == end:
            return [start]
        
        visited = {start}
        queue = deque([(start, [start])])
        
        while queue:
            vertex, path = queue.popleft()
            
            for neighbor, _ in self.adjacency_list[vertex]:
                if neighbor == end:
                    return path + [neighbor]
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        
        return None
    
    def is_bipartite(self):
        """Kiểm tra xem đồ thị có phải 2 phía hay không"""
        if not self.vertices:
            return True
        
        color = {}
        
        def bfs_check(start):
            queue = deque([start])
            color[start] = 0
            
            while queue:
                u = queue.popleft()
                for v, _ in self.adjacency_list[u]:
                    if v not in color:
                        color[v] = 1 - color[u]
                        queue.append(v)
                    elif color[v] == color[u]:
                        return False
            return True
        
        for vertex in self.vertices:
            if vertex not in color:
                if not bfs_check(vertex):
                    return False
        
        return True
    
    def dijkstra(self, start):
        """Thuật toán Dijkstra tìm đường đi ngắn nhất"""
        distances = {v: float('inf') for v in self.vertices}
        distances[start] = 0
        visited = set()
        
        while len(visited) < len(self.vertices):
            min_dist = float('inf')
            min_vertex = None
            
            for v in self.vertices:
                if v not in visited and distances[v] < min_dist:
                    min_dist = distances[v]
                    min_vertex = v
            
            if min_vertex is None:
                break
            
            visited.add(min_vertex)
            
            for neighbor, weight in self.adjacency_list[min_vertex]:
                if neighbor not in visited:
                    distances[neighbor] = min(
                        distances[neighbor],
                        distances[min_vertex] + weight
                    )
        
        return distances


    def prim_mst(self):
        """Thuật toán Prim - Minimum Spanning Tree"""
        if self.is_directed:
            raise ValueError("Prim chỉ áp dụng cho đồ thị vô hướng")

        if not self.vertices:
            return []

        visited = set()
        start = next(iter(self.vertices))
        visited.add(start)
        mst = []

        edges = []
        for v, w in self.adjacency_list[start]:
            edges.append((w, start, v))

        while edges and len(visited) < len(self.vertices):
            edges.sort()
            weight, u, v = edges.pop(0)

            if v in visited:
                continue

            visited.add(v)
            mst.append((u, v, weight))

            for to, w in self.adjacency_list[v]:
                if to not in visited:
                    edges.append((w, v, to))

        return mst

    def kruskal_mst(self):
        """Thuật toán Kruskal - Minimum Spanning Tree"""
        if self.is_directed:
            raise ValueError("Kruskal chỉ áp dụng cho đồ thị vô hướng")

        parent = {}
        rank = {}

        def find(u):
            if parent[u] != u:
                parent[u] = find(parent[u])
            return parent[u]

        def union(u, v):
            ru, rv = find(u), find(v)
            if ru == rv:
                return False
            if rank[ru] < rank[rv]:
                parent[ru] = rv
            else:
                parent[rv] = ru
                if rank[ru] == rank[rv]:
                    rank[ru] += 1
            return True

        for v in self.vertices:
            parent[v] = v
            rank[v] = 0

        mst = []
        edges = sorted(self.edge_list, key=lambda x: x[2])

        for u, v, w in edges:
            if union(u, v):
                mst.append((u, v, w))

        return mst


    def ford_fulkerson(self, source, sink):
        """Thuật toán Ford-Fulkerson (Edmonds-Karp)"""
        if not self.is_directed:
            raise ValueError("Ford-Fulkerson chỉ áp dụng cho đồ thị có hướng")

        # Tạo đồ thị thặng dư
        residual = defaultdict(lambda: defaultdict(int))
        for u, v, w in self.edge_list:
            residual[u][v] += w      # cộng dồn nếu có nhiều cạnh
            residual[v][u] += 0      # tạo cạnh ngược

        max_flow = 0

        def bfs():
            parent = {source: None}
            queue = deque([source])

            while queue:
                u = queue.popleft()
                for v in residual[u]:
                    if v not in parent and residual[u][v] > 0:
                        parent[v] = u
                        if v == sink:
                            return parent
                        queue.append(v)
            return None

        while True:
            parent = bfs()
            if parent is None:
                break

            # Tìm luồng nhỏ nhất trên đường tăng
            path_flow = float('inf')
            v = sink
            while v != source:
                u = parent[v]
                path_flow = min(path_flow, residual[u][v])
                v = u

            # Cập nhật đồ thị thặng dư
            v = sink
            while v != source:
                u = parent[v]
                residual[u][v] -= path_flow
                residual[v][u] += path_flow
                v = u

            max_flow += path_flow

        return max_flow


        def is_eulerian(self):
            """Trả về:
        0: không có đường đi/chu trình Euler
        1: có đường đi Euler (nhưng không phải chu trình)
        2: có chu trình Euler
        """
        if self.is_directed:
            # Với đồ thị có hướng cần kiểm tra bậc vào = bậc ra cho mọi đỉnh
            # (code này chỉ hỗ trợ vô hướng → tạm trả về 0)
            return 0

        odd_degree_count = 0
        for v in self.vertices:
            if len(self.adjacency_list[v]) % 2 == 1:
                odd_degree_count += 1

        if odd_degree_count == 0:
            return 2
        if odd_degree_count == 2:
            return 1
        return 0

def has_euler_cycle(self):
    """Kiểm tra có chu trình Euler hay không
    - Vô hướng: tất cả bậc chẵn + liên thông yếu
    - Có hướng: mọi đỉnh in-degree = out-degree + mạnh liên thông
    """
    if not self.vertices:
        return False

    if not self.is_directed:
        # Code cũ cho đồ thị vô hướng (giữ nguyên)
        for v in self.vertices:
            if len(self.adjacency_list[v]) % 2 != 0:
                return False

        non_isolated_vertices = {v for v in self.vertices if self.adjacency_list[v]}
        if not non_isolated_vertices:
            return True

        start = next(iter(non_isolated_vertices))
        visited = set()
        stack = [start]
        while stack:
            u = stack.pop()
            if u not in visited:
                visited.add(u)
                for v, _ in self.adjacency_list[u]:
                    if v not in visited:
                        stack.append(v)

        for v in non_isolated_vertices:
            if v not in visited:
                return False

        return True

    else:
        # Đồ thị có hướng: kiểm tra in-degree == out-degree cho mọi đỉnh
        in_degree = defaultdict(int)
        out_degree = defaultdict(int)

        for u in self.vertices:
            out_degree[u] = len(self.adjacency_list[u])
            for v, _ in self.adjacency_list[u]:
                in_degree[v] += 1

        # Đảm bảo mọi đỉnh đều được tính (kể cả đỉnh không có cạnh ra/vào)
        for v in self.vertices:
            if in_degree[v] != out_degree[v]:
                return False

        # LƯU Ý: Chưa kiểm tra mạnh liên thông (strong connectivity)
        # Hiện tại tạm chấp nhận nếu in=out cho mọi đỉnh
        # Nếu muốn chính xác hơn, cần thêm thuật toán Kosaraju hoặc Tarjan
        # (phần này có thể bổ sung sau)

        return True

    def hierholzer(self, start=None):
        """Tìm chu trình Euler bằng thuật toán Hierholzer
        Trả về: list các đỉnh theo thứ tự chu trình hoặc None nếu không tồn tại
        """
        if not self.has_euler_cycle():
            return None

        # Chọn đỉnh bắt đầu (ưu tiên đỉnh có cạnh)
        if start is None:
            for v in self.vertices:
                if self.adjacency_list[v]:
                    start = v
                    break
            else:
                return []  # đồ thị rỗng hoặc chỉ có đỉnh cô lập

        # Tạo bản sao sâu của adjacency list (quan trọng!)
        from copy import deepcopy
        temp_adj = deepcopy(self.adjacency_list)  # an toàn nhất

        stack = []
        circuit = []

        stack.append(start)

        while stack:
            u = stack[-1]

        if temp_adj[u]:  # còn cạnh chưa đi
            # Lấy một cạnh bất kỳ
            v, _ = temp_adj[u].pop()

            if not self.is_directed:
                # Chỉ xóa cạnh ngược nếu là đồ thị vô hướng
                for i, (nei, _) in enumerate(temp_adj[v]):
                    if nei == u:
                        del temp_adj[v][i]
                        break

            stack.append(v)
        else:
            # Không còn cạnh → đưa vào circuit
            circuit.append(stack.pop())

        circuit.reverse()

        # Kiểm tra xem đã dùng hết cạnh chưa
        edges_used = len(circuit) - 1
        total_edges = sum(len(neighbors) for neighbors in self.adjacency_list.values()) // 2

        if edges_used != total_edges:
            return None  # không liên thông hoặc lỗi

        return circuit

    def fleury_algorithm(self):
        """Thuật toán Fleury tìm đường đi / chu trình Euler"""
        if self.is_directed:
            raise ValueError("Fleury chỉ áp dụng cho đồ thị vô hướng")

        check = self.is_eulerian()
        if check == 0:
            return None, "Đồ thị không có Euler"

        # Copy adjacency list (chỉ lưu đỉnh kề)
        graph = defaultdict(list)
        for u in self.adjacency_list:
            for v, _ in self.adjacency_list[u]:
                graph[u].append(v)

        # Chọn đỉnh bắt đầu
        start = next(iter(self.vertices))
        if check == 1:
            for v in graph:
                if len(graph[v]) % 2 != 0:
                    start = v
                    break

        path = [start]

        def dfs_count(u, visited):
            visited.add(u)
            for v in graph[u]:
                if v not in visited:
                    dfs_count(v, visited)

        def is_bridge(u, v):
            if len(graph[u]) == 1:
                return False

            visited1 = set()
            dfs_count(u, visited1)
            count1 = len(visited1)

            # Xóa cạnh
            graph[u].remove(v)
            graph[v].remove(u)

            visited2 = set()
            dfs_count(u, visited2)
            count2 = len(visited2)

            # Khôi phục
            graph[u].append(v)
            graph[v].append(u)

            return count2 < count1

        curr = start
        total_edges = sum(len(graph[v]) for v in graph) // 2

        while total_edges > 0:
            for v in list(graph[curr]):
                if not is_bridge(curr, v) or len(graph[curr]) == 1:
                    graph[curr].remove(v)
                    graph[v].remove(curr)
                    path.append(v)
                    curr = v
                    total_edges -= 1
                    break

        return path, "Thành công"



# ============ ỨNG DỤNG TKINTER =============
class GraphApp:
    """Ứng dụng Tkinter cho đồ thị"""
    
    def __init__(self, root):
        self.root = root
        self.root.geometry("1400x900")
        
        self.graph = Graph(is_directed=False)
        self.nx_graph = nx.Graph()
        self.pos = {}
        self.mode = None
        self.canvas = None
        
        self.setup_ui()
    
    def setup_ui(self):
        """Thiết lập giao diện"""
        # Frame chính
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Frame điều khiển bên trái với scroll
        scrollable_frame = ttk.Frame(main_frame)
        scrollable_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)
        
        self.canvas_scroll = tk.Canvas(scrollable_frame, width=350, height=800)
        scrollbar = ttk.Scrollbar(scrollable_frame, orient="vertical", command=self.canvas_scroll.yview)
        self.canvas_scroll.configure(yscrollcommand=scrollbar.set)
        
        scrollbar.pack(side="right", fill="y")
        self.canvas_scroll.pack(side="left", fill="both", expand=True)
        
        control_frame = ttk.Frame(self.canvas_scroll)
        self.canvas_scroll.create_window((0, 0), window=control_frame, anchor="nw")
        
        control_frame.bind("<Configure>", self.on_frame_configure)
        self.canvas_scroll.bind("<MouseWheel>", self._on_mousewheel)
        
        # Frame hiển thị đồ thị bên phải
        display_frame = ttk.Frame(main_frame)
        display_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        ttk.Label(control_frame, text="=== THÊM PHẦN TỬ ===", font=('Arial', 10, 'bold')).pack(pady=10)
        
        # Thêm đỉnh
        add_vertex_frame = ttk.Frame(control_frame)
        add_vertex_frame.pack(fill='x', padx=10, pady=5)
        ttk.Button(add_vertex_frame, text="Thêm đỉnh (click)", command=self.start_add_vertex).pack()
        
        # Thêm cạnh
        add_edge_frame = ttk.Frame(control_frame)
        add_edge_frame.pack(fill='x', padx=10, pady=5)
        ttk.Label(add_edge_frame, text="Đỉnh từ:").grid(row=0, column=0, sticky='w', pady=2)
        self.from_vertex_entry = ttk.Entry(add_edge_frame)
        self.from_vertex_entry.grid(row=0, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Label(add_edge_frame, text="Đỉnh đến:").grid(row=1, column=0, sticky='w', pady=2)
        self.to_vertex_entry = ttk.Entry(add_edge_frame)
        self.to_vertex_entry.grid(row=1, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Label(add_edge_frame, text="Trọng số:").grid(row=2, column=0, sticky='w', pady=2)
        self.weight_entry = ttk.Entry(add_edge_frame)
        self.weight_entry.insert(0, "1")
        self.weight_entry.grid(row=2, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Button(add_edge_frame, text="Thêm cạnh", command=self.add_edge).grid(row=3, column=0, columnspan=2, pady=5)
        
        add_edge_frame.columnconfigure(1, weight=1)
        
        # Xóa đỉnh
        delete_vertex_frame = ttk.Frame(control_frame)
        delete_vertex_frame.pack(fill='x', padx=10, pady=5)
        ttk.Label(delete_vertex_frame, text="Tên đỉnh xóa:").grid(row=0, column=0, sticky='w', pady=2)
        self.delete_vertex_entry = ttk.Entry(delete_vertex_frame)
        self.delete_vertex_entry.grid(row=0, column=1, sticky='ew', pady=2, padx=(5,0))
        ttk.Button(delete_vertex_frame, text="Xóa đỉnh", command=self.delete_vertex).grid(row=1, column=0, columnspan=2, pady=5)
        delete_vertex_frame.columnconfigure(1, weight=1)
        
        # Xóa cạnh
        delete_edge_frame = ttk.Frame(control_frame)
        delete_edge_frame.pack(fill='x', padx=10, pady=5)
        ttk.Label(delete_edge_frame, text="Đỉnh từ:").grid(row=0, column=0, sticky='w', pady=2)
        self.delete_from_entry = ttk.Entry(delete_edge_frame)
        self.delete_from_entry.grid(row=0, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Label(delete_edge_frame, text="Đỉnh đến:").grid(row=1, column=0, sticky='w', pady=2)
        self.delete_to_entry = ttk.Entry(delete_edge_frame)
        self.delete_to_entry.grid(row=1, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Button(delete_edge_frame, text="Xóa cạnh", command=self.delete_edge).grid(row=2, column=0, columnspan=2, pady=5)
        delete_edge_frame.columnconfigure(1, weight=1)
        
        # Loại đồ thị
        ttk.Label(control_frame, text="=== LOẠI ĐỒ THỊ ===", font=('Arial', 10, 'bold')).pack(pady=10)
        graph_type_frame = ttk.Frame(control_frame)
        graph_type_frame.pack(fill='x', padx=10, pady=10)
        ttk.Label(graph_type_frame, text="Loại đồ thị:", font=('Arial', 10)).grid(row=0, column=0, sticky='w', pady=2)
        self.graph_type_var = tk.StringVar(value="undirected")
        ttk.Radiobutton(graph_type_frame, text="Vô hướng", variable=self.graph_type_var, 
                       value="undirected", command=self.change_graph_type).grid(row=1, column=0, sticky='w', pady=2)
        ttk.Radiobutton(graph_type_frame, text="Có hướng", variable=self.graph_type_var, 
                       value="directed", command=self.change_graph_type).grid(row=2, column=0, sticky='w', pady=2)
        
        # Phân tích
        ttk.Label(control_frame, text="=== PHÂN TÍCH ===", font=('Arial', 10, 'bold')).pack(pady=10)
        analysis_frame = ttk.Frame(control_frame)
        analysis_frame.pack(fill='x', padx=10, pady=10)
        ttk.Label(analysis_frame, text="Đỉnh bắt đầu (BFS/DFS):").grid(row=0, column=0, sticky='w', pady=2)
        self.start_vertex_entry = ttk.Entry(analysis_frame)
        self.start_vertex_entry.grid(row=0, column=1, sticky='ew', pady=2, padx=(5,0))
        
        ttk.Button(analysis_frame, text="BFS", command=self.perform_bfs).grid(row=1, column=0, pady=3)
        ttk.Button(analysis_frame, text="DFS", command=self.perform_dfs).grid(row=1, column=1, pady=3)
        
        ttk.Label(analysis_frame, text="Tìm đường đi (từ -> đến):").grid(row=2, column=0, columnspan=2, sticky='w', pady=10)
        self.path_from_entry = ttk.Entry(analysis_frame)
        self.path_from_entry.grid(row=3, column=0, sticky='ew', pady=3)
        self.path_to_entry = ttk.Entry(analysis_frame)
        self.path_to_entry.grid(row=3, column=1, sticky='ew', pady=3, padx=(5,0))
        ttk.Button(analysis_frame, text="Đường ngắn nhất", command=self.find_shortest_path).grid(row=4, column=0, columnspan=2, pady=5)
        
        ttk.Button(analysis_frame, text="Kiểm tra 2 phía", command=self.check_bipartite).grid(row=5, column=0, columnspan=2, pady=5)
        analysis_frame.columnconfigure(1, weight=1)


        # ===== NÂNG CAO (MST) =====
        ttk.Label(control_frame, text="=== NÂNG CAO (MST) ===", font=('Arial', 10, 'bold')).pack(pady=10)
        ttk.Button(control_frame, text="Prim", command=self.run_prim).pack(pady=3)
        ttk.Button(control_frame, text="Kruskal", command=self.run_kruskal).pack(pady=3)
        ttk.Button(control_frame, text="Ford-Fulkerson (Max Flow)", command=self.run_ford_fulkerson).pack(pady=3) 
        ttk.Button(control_frame, text="Fleury (Euler)", command=self.run_fleury).pack(pady=3)
        ttk.Button(control_frame,    text="Hierholzer (Euler)",    command=self.find_euler_cycle).pack(pady=3)



        
        # Chuyển đổi biểu diễn
        ttk.Label(control_frame, text="=== CHUYỂN ĐỔI ===", font=('Arial', 10, 'bold')).pack(pady=10)
        conversion_frame = ttk.Frame(control_frame)
        conversion_frame.pack(fill='x', padx=10, pady=10)
        ttk.Button(conversion_frame, text="→ Ma trận kề", command=self.show_adjacency_matrix).grid(row=0, column=0, pady=3)
        ttk.Button(conversion_frame, text="→ Danh sách kề", command=self.show_adjacency_list).grid(row=0, column=1, pady=3)
        ttk.Button(conversion_frame, text="→ Danh sách cạnh", command=self.show_edge_list).grid(row=1, column=0, columnspan=2, pady=3)
        
        # Điều khiển tệp
        ttk.Label(control_frame, text="=== TỆP ===", font=('Arial', 10, 'bold')).pack(pady=10)
        file_frame = ttk.Frame(control_frame)
        file_frame.pack(fill='x', padx=10, pady=10)
        ttk.Button(file_frame, text="Lưu đồ thị", command=self.save_graph).grid(row=0, column=0, pady=3)
        ttk.Button(file_frame, text="Tải đồ thị", command=self.load_graph).grid(row=0, column=1, pady=3)
        ttk.Button(file_frame, text="Xóa tất cả", command=self.clear_graph).grid(row=1, column=0, columnspan=2, pady=5)
        
        # ===== PHẦN HIỂN THỊ =====
        self.canvas_frame = ttk.Frame(display_frame)
        self.canvas_frame.pack(fill=tk.BOTH, expand=True)
        
        # Kết quả
        result_frame = ttk.LabelFrame(display_frame, text="Kết quả", padding=5)
        result_frame.pack(fill=tk.X, pady=5)
        
        self.result_text = tk.Text(result_frame, height=8, width=50)
        self.result_text.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = ttk.Scrollbar(result_frame, command=self.result_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.result_text.config(yscrollcommand=scrollbar.set)
        
        self.draw_graph()
    
    def on_frame_configure(self, event):
        """Cập nhật scrollregion khi frame thay đổi"""
        self.canvas_scroll.configure(scrollregion=self.canvas_scroll.bbox("all"))
    
    def _on_mousewheel(self, event):
        """Cuộn canvas bằng chuột"""
        self.canvas_scroll.yview_scroll(int(-1 * (event.delta / 120)), "units")
    
    def change_graph_type(self):
        """Thay đổi loại đồ thị"""
        is_directed = self.graph_type_var.get() == "directed"
        self.graph.is_directed = is_directed
        self.nx_graph = nx.DiGraph() if is_directed else nx.Graph()
        
        for vertex in self.graph.vertices:
            self.nx_graph.add_node(vertex)
        
        for u, v, weight in self.graph.edge_list:
            if weight == 1:
                self.nx_graph.add_edge(u, v)
            else:
                self.nx_graph.add_edge(u, v, weight=weight)
        
        self.draw_graph()
        graph_type_name = "có hướng" if is_directed else "vô hướng"
        self.log_result(f"✓ Đổi thành đồ thị {graph_type_name}")
    
    def perform_bfs(self):
        """Thực hiện BFS"""
        start = self.start_vertex_entry.get().strip()
        if not start:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập đỉnh bắt đầu!")
            return
        
        if start not in self.graph.vertices:
            messagebox.showerror("Lỗi", f"Đỉnh '{start}' không tồn tại!")
            return
        
        result = self.graph.bfs(start)
        result_str = " → ".join(str(v) for v in result)
        self.log_result(f"BFS từ '{start}':\n{result_str}")

    
    def is_eulerian(self):
        """0: không Euler | 1: đường đi Euler | 2: chu trình Euler"""
        odd = 0
        for v in self.vertices:
            if len(self.adjacency_list[v]) % 2 != 0:
                odd += 1

        if odd == 0:
            return 2
        if odd == 2:
            return 1
        return 0


    def has_euler_cycle(self):
        """Kiểm tra đồ thị vô hướng có chu trình Euler"""
        if self.is_directed:
            return False

        if not self.vertices:
            return False

        # Kiểm tra bậc chẵn
        for v in self.vertices:
            if len(self.adjacency_list[v]) % 2 != 0:
                return False

        # Kiểm tra liên thông (bỏ đỉnh cô lập)
        start = None
        for v in self.vertices:
            if self.adjacency_list[v]:
                start = v
                break

        if start is None:
            return True

        visited = set()
        stack = [start]

        while stack:
            u = stack.pop()
            if u not in visited:
                visited.add(u)
                for v, _ in self.adjacency_list[u]:
                    if v not in visited:
                        stack.append(v)

        for v in self.vertices:
            if self.adjacency_list[v] and v not in visited:
                return False

        return True


    def hierholzer(self, start=None):
        """Thuật toán Hierholzer tìm chu trình Euler"""
        if not self.has_euler_cycle():
            return None

        if start is None:
            for v in self.vertices:
                if self.adjacency_list[v]:
                    start = v
                    break

        temp_adj = {u: list(self.adjacency_list[u]) for u in self.vertices}
        stack = [start]
        circuit = []

        while stack:
            u = stack[-1]
            if temp_adj[u]:
                v, _ = temp_adj[u].pop()
                for i, (x, _) in enumerate(temp_adj[v]):
                    if x == u:
                        temp_adj[v].pop(i)
                        break
                stack.append(v)
            else:
                circuit.append(stack.pop())

        circuit.reverse()
        return circuit


    
    def perform_dfs(self):
        """Thực hiện DFS"""
        start = self.start_vertex_entry.get().strip()
        if not start:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập đỉnh bắt đầu!")
            return
        
        if start not in self.graph.vertices:
            messagebox.showerror("Lỗi", f"Đỉnh '{start}' không tồn tại!")
            return
        
        result = self.graph.dfs(start)
        result_str = " → ".join(str(v) for v in result)
        self.log_result(f"DFS từ '{start}':\n{result_str}")
    
    def find_shortest_path(self):
        """Tìm đường đi ngắn nhất"""
        start = self.path_from_entry.get().strip()
        end = self.path_to_entry.get().strip()
        
        if not start or not end:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập cả hai đỉnh!")
            return
        
        if start not in self.graph.vertices or end not in self.graph.vertices:
            messagebox.showerror("Lỗi", "Một hoặc cả hai đỉnh không tồn tại!")
            return
        
        path = self.graph.shortest_path_bfs(start, end)
        if path:
            path_str = " → ".join(str(v) for v in path)
            self.log_result(f"Đường đi ngắn nhất từ '{start}' đến '{end}':\n{path_str}\nĐộ dài: {len(path)-1} cạnh")
        else:
            self.log_result(f"Không có đường đi từ '{start}' đến '{end}'")
    
    def check_bipartite(self):
        """Kiểm tra đồ thị 2 phía"""
        if not self.graph.vertices:
            messagebox.showinfo("Thông tin", "Đồ thị trống!")
            return
        
        is_bipartite = self.graph.is_bipartite()
        if is_bipartite:
            self.log_result("✓ Đồ thị này LÀ đồ thị 2 phía (Bipartite)")
        else:
            self.log_result("✗ Đồ thị này KHÔNG phải đồ thị 2 phía")
    
    def show_adjacency_matrix(self):
        """Hiển thị ma trận kề"""
        if not self.graph.vertices:
            messagebox.showinfo("Thông tin", "Đồ thị trống!")
            return
        
        matrix, vertices_list = self.graph.to_adjacency_matrix()
        
        result_str = "Ma trận kề:\n\n"
        # Tạo bảng (n+1) x (n+1)
        table = [[''] + vertices_list]  # Row 0: empty + vertices
        for i, v in enumerate(vertices_list):
            row = [v] + [str(matrix[i][j]) for j in range(len(vertices_list))]
            table.append(row)
        
        # Format với width 4 cho mỗi cell, căn giữa
        for row in table:
            result_str += " | ".join(f"{cell:^4}" for cell in row) + "\n"
            if table.index(row) == 0:  # Sau header, thêm đường kẻ
                result_str += "-" * (6 * len(vertices_list) + 3) + "\n"
        
        self.log_result(result_str)
    
    def show_edge_list(self):
        """Hiển thị danh sách cạnh"""
        if not self.graph.edge_list:
            self.log_result("Danh sách cạnh trống")
            return
        
        result_str = "Danh sách cạnh:\n\n"
        result_str += "Từ  |  Đến  |  Trọng số\n"
        result_str += "------|-------|----------\n"
        for u, v, weight in self.graph.edge_list:
            result_str += f"{str(u):4s} | {str(v):5s} | {weight}\n"
        
        self.log_result(result_str)
    
    def show_adjacency_list(self):
        """Hiển thị danh sách kề"""
        if not self.graph.vertices:
            messagebox.showinfo("Thông tin", "Đồ thị trống!")
            return
        
        result_str = "Danh sách kề:\n\n"
        for vertex in sorted(self.graph.vertices):
            neighbors = [v for v, w in self.graph.adjacency_list[vertex]]
            result_str += f"{vertex}: {{{', '.join(neighbors) if neighbors else ''}}}\n"
        
        self.log_result(result_str)
    
    def draw_graph(self):
        """Vẽ đồ thị"""
        for widget in self.canvas_frame.winfo_children():
            widget.destroy()
        
        fig = Figure(figsize=(8, 6), dpi=100)
        ax = fig.add_subplot(111)
        
        # Set axes limits to match canvas size for pixel coordinates
        ax.set_xlim(0, 800)
        ax.set_ylim(600, 0)
        
        if self.graph.vertices:
            # Tính toán vị trí nút
            if not self.pos or len(self.pos) != len(self.nx_graph.nodes()):
                self.pos = nx.spring_layout(self.nx_graph, k=2, iterations=50)
            
            # Vẽ nút
            nx.draw_networkx_nodes(self.nx_graph, self.pos, node_color='lightblue', 
                                   node_size=800, ax=ax)
            
            # Vẽ cạnh
            nx.draw_networkx_edges(self.nx_graph, self.pos, ax=ax, 
                                  arrowsize=20, arrowstyle='->' if self.graph.is_directed else '-',
                                  connectionstyle="arc3,rad=0.1")
            
            # Vẽ nhãn
            nx.draw_networkx_labels(self.nx_graph, self.pos, font_size=10, font_weight='bold', ax=ax)
            
            # Vẽ trọng số
            edge_labels = {}
            for u, v, data in self.nx_graph.edges(data=True):
                if 'weight' in data and data['weight'] != 1:
                    edge_labels[(u, v)] = data['weight']
            
            if edge_labels:
                nx.draw_networkx_edge_labels(self.nx_graph, self.pos, edge_labels, ax=ax)
            
            ax.set_title(f"Đồ thị ({'Có hướng' if self.graph.is_directed else 'Vô hướng'})")
        else:
            ax.set_title("Đồ thị trống - Click để thêm đỉnh")
        
        ax.axis('off')
        
        canvas = FigureCanvasTkAgg(fig, master=self.canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        self.canvas = canvas
        self.canvas.mpl_connect('button_press_event', self.on_canvas_click)
    
    def start_add_vertex(self):
        """Bắt đầu chế độ thêm đỉnh"""
        self.mode = 'add_vertex'
        self.log_result("Click vào vị trí trên canvas để đặt đỉnh mới")
    
    def add_edge(self):
        """Thêm cạnh"""
        from_v = self.from_vertex_entry.get().strip()
        to_v = self.to_vertex_entry.get().strip()
        
        if not from_v or not to_v:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập cả hai đỉnh!")
            return
        
        if from_v not in self.graph.vertices or to_v not in self.graph.vertices:
            messagebox.showwarning("Cảnh báo", "Một hoặc cả hai đỉnh không tồn tại!")
            return
        
        try:
            weight = float(self.weight_entry.get())
        except ValueError:
            weight = 1
        
        # Check if edge already exists
        exists = any((uu == from_v and vv == to_v) or (not self.graph.is_directed and uu == to_v and vv == from_v) for uu, vv, _ in self.graph.edge_list)
        if exists:
            messagebox.showwarning("Cảnh báo", f"Cạnh '{from_v}' -> '{to_v}' đã tồn tại!")
            return
        
        self.graph.add_edge(from_v, to_v, weight)
        
        if weight == 1:
            self.nx_graph.add_edge(from_v, to_v)
        else:
            self.nx_graph.add_edge(from_v, to_v, weight=weight)
        
        self.from_vertex_entry.delete(0, tk.END)
        self.to_vertex_entry.delete(0, tk.END)
        self.weight_entry.delete(0, tk.END)
        self.weight_entry.insert(0, "1")
        self.draw_graph()
        self.log_result(f"✓ Thêm cạnh '{from_v}' -> '{to_v}' (trọng số: {weight}) thành công")
    
    def delete_vertex(self):
        """Xóa đỉnh"""
        vertex = self.delete_vertex_entry.get().strip()
        if not vertex:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập tên đỉnh!")
            return
        
        if vertex not in self.graph.vertices:
            messagebox.showwarning("Cảnh báo", f"Đỉnh '{vertex}' không tồn tại!")
            return
        
        if messagebox.askyesno("Xác nhận", f"Xóa đỉnh '{vertex}' và tất cả cạnh liên quan?"):
            # Remove from graph
            self.graph.vertices.discard(vertex)
            self.graph.adjacency_list.pop(vertex, None)
            # Remove edges from edge_list
            self.graph.edge_list = [(u,v,w) for u,v,w in self.graph.edge_list if u != vertex and v != vertex]
            # Remove from adjacency lists of other vertices
            for v in list(self.graph.adjacency_list.keys()):
                self.graph.adjacency_list[v] = [(adj_v, w) for adj_v, w in self.graph.adjacency_list[v] if adj_v != vertex]
            self.nx_graph.remove_node(vertex)
            if vertex in self.pos:
                del self.pos[vertex]
            self.delete_vertex_entry.delete(0, tk.END)
            self.draw_graph()
            self.log_result(f"✓ Xóa đỉnh '{vertex}' thành công")
    
    def delete_edge(self):
        """Xóa cạnh"""
        from_v = self.delete_from_entry.get().strip()
        to_v = self.delete_to_entry.get().strip()
        
        if not from_v or not to_v:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập cả hai đỉnh!")
            return
        
        # Find and remove edge
        found = False
        for i, (uu, vv, ww) in enumerate(self.graph.edge_list):
            if (uu == from_v and vv == to_v) or (not self.graph.is_directed and uu == to_v and vv == from_v):
                del self.graph.edge_list[i]
                # Remove from adjacency
                self.graph.adjacency_list[from_v] = [(vtx, w) for vtx, w in self.graph.adjacency_list[from_v] if vtx != to_v]
                if not self.graph.is_directed:
                    self.graph.adjacency_list[to_v] = [(vtx, w) for vtx, w in self.graph.adjacency_list[to_v] if vtx != from_v]
                self.nx_graph.remove_edge(from_v, to_v)
                found = True
                break
        
        if found:
            self.delete_from_entry.delete(0, tk.END)
            self.delete_to_entry.delete(0, tk.END)
            self.draw_graph()
            self.log_result(f"✓ Xóa cạnh '{from_v}' -> '{to_v}' thành công")
        else:
            messagebox.showwarning("Cảnh báo", f"Không tìm thấy cạnh '{from_v}' -> '{to_v}'")
    
    def on_canvas_click(self, event):
        """Xử lý click trên canvas"""
        if not event.inaxes:
            return
        
        x, y = event.xdata, event.ydata
        
        if self.mode == 'add_vertex':
            # Mở dialog nhập tên
            name = simpledialog.askstring("Nhập tên đỉnh", "Nhập tên cho đỉnh mới:")
            if name and name.strip():
                name = name.strip()
                if name in self.graph.vertices:
                    messagebox.showwarning("Cảnh báo", f"Đỉnh '{name}' đã tồn tại!")
                    return
                self.graph.add_vertex(name)
                self.nx_graph.add_node(name)
                # Set position
                self.pos[name] = (x, y)
                self.draw_graph()
                self.log_result(f"✓ Thêm đỉnh '{name}' thành công")
            self.mode = None
    
    def log_result(self, message):
        """Ghi kết quả vào khu vực text"""
        self.result_text.config(state=tk.NORMAL)
        self.result_text.delete(1.0, tk.END)
        self.result_text.insert(tk.END, message)
        self.result_text.config(state=tk.DISABLED)
    
    def save_graph(self):
        """Lưu đồ thị"""
        file_path = filedialog.asksaveasfilename(defaultextension=".graph",
                                                 filetypes=[("Graph files", "*.graph"), ("All files", "*.*")])
        if not file_path:
            return
        
        data = {
            'is_directed': self.graph.is_directed,
            'vertices': list(self.graph.vertices),
            'edges': self.graph.edge_list,
            'adjacency_list': dict(self.graph.adjacency_list),
            'pos': self.pos
        }
        
        try:
            with open(file_path, 'wb') as f:
                pickle.dump(data, f)
            self.log_result(f"✓ Đồ thị đã được lưu vào:\n{file_path}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể lưu: {str(e)}")
    
    def load_graph(self):
        """Tải đồ thị"""
        file_path = filedialog.askopenfilename(filetypes=[("Graph files", "*.graph"), ("All files", "*.*")])
        if not file_path:
            return
        
        try:
            with open(file_path, 'rb') as f:
                data = pickle.load(f)
            
            self.graph = Graph(is_directed=data['is_directed'])
            self.nx_graph = nx.DiGraph() if data['is_directed'] else nx.Graph()
            
            for edge in data['edges']:
                u, v, weight = edge
                self.graph.add_edge(u, v, weight)
                if weight == 1:
                    self.nx_graph.add_edge(u, v)
                else:
                    self.nx_graph.add_edge(u, v, weight=weight)
            
            self.pos = data.get('pos', {})
            self.change_graph_type()
            self.log_result(f"✓ Đồ thị đã được tải từ:\n{file_path}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể tải: {str(e)}")
    
    def clear_graph(self):
        """Xóa tất cả"""
        if messagebox.askyesno("Xác nhận", "Xóa tất cả đỉnh và cạnh?"):
            self.graph = Graph(is_directed=self.graph.is_directed)
            self.nx_graph = nx.DiGraph() if self.graph.is_directed else nx.Graph()
            self.pos = {}
            self.draw_graph()
            self.log_result("✓ Đồ thị đã được xóa")


    def run_prim(self):
        try:
            mst = self.graph.prim_mst()
            self.highlight_mst(mst, "Prim")
        except ValueError as e:
            messagebox.showerror("Lỗi", str(e))
    def find_euler_cycle(self):
        if not self.graph.vertices:
            messagebox.showwarning("Cảnh báo", "Đồ thị trống!")
            return

    # XÓA hoặc COMMENT dòng chặn có hướng
    # if self.graph.is_directed:
    #     messagebox.showwarning("Cảnh báo", "Hierholzer hiện chỉ hỗ trợ đồ thị vô hướng!")
    #     return

    cycle = self.graph.hierholzer()
    if cycle is None:
        messagebox.showwarning("Cảnh báo", "Đồ thị không có chu trình Euler!\n(Kiểm tra: bậc vào/ra bằng nhau và liên thông mạnh)")
        return

    if not cycle:
        self.log_result("Đồ thị không có cạnh → chu trình Euler rỗng.")
        return

    result = " → ".join(map(str, cycle))
    graph_type = "có hướng" if self.graph.is_directed else "vô hướng"
    self.log_result(f"Chu trình Euler (Hierholzer - {graph_type}):\n{result}\n\n"
                    f"(Bắt đầu từ {cycle[0]}, quay về {cycle[-1]})")
    def run_kruskal(self):
        try:
            mst = self.graph.kruskal_mst()
            self.highlight_mst(mst, "Kruskal")
        except ValueError as e:
            messagebox.showerror("Lỗi", str(e))

    def highlight_mst(self, mst, name):
        if not mst:
            self.log_result("Không thể tạo MST")
            return

        self.draw_graph()

        fig = plt.gcf()
        ax = plt.gca()

        mst_edges = [(u, v) for u, v, _ in mst]
        nx.draw_networkx_edges(
            self.nx_graph,
            self.pos,
            edgelist=mst_edges,
            edge_color='red',
            width=3,
            ax=ax
        )

        total_weight = sum(w for _, _, w in mst)
        result = f"{name} - Minimum Spanning Tree:\n"
        for u, v, w in mst:
            result += f"{u} - {v} (w={w})\n"
        result += f"Tổng trọng số = {total_weight}"

        self.log_result(result)


    def run_ford_fulkerson(self):
        start = self.path_from_entry.get().strip()
        end = self.path_to_entry.get().strip()
        
        if not start or not end:
            messagebox.showwarning("Cảnh báo", "Nhập đỉnh bắt đầu và kết thúc (ô tìm đường đi)!")
            return
            
        try:
            max_flow = self.graph.ford_fulkerson(start, end)
            self.log_result(f"Luồng cực đại (Max Flow) từ {start} -> {end}: {max_flow}")
        except Exception as e:
            messagebox.showerror("Lỗi", str(e))

    def run_fleury(self):
        try:
            path, msg = self.graph.fleury_algorithm()
            if path:
                path_str = " -> ".join(map(str, path))
                self.log_result(f"Kết quả Euler (Fleury):\n{path_str}")
                self.draw_graph() 
            else:
                self.log_result(f"Không tìm thấy: {msg}")
        except Exception as e:
            messagebox.showerror("Lỗi", str(e))


def main():
    """Chương trình chính"""
    root = tk.Tk()
    app = GraphApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
