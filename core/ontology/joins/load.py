"""Load a repo script as a module by path, without running its main. Used by the join scripts here."""
import importlib.util, os
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
def load(path):
    s = importlib.util.spec_from_file_location(path.replace("/", "_")[:-3], os.path.join(ROOT, path))
    m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
