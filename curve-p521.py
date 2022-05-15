from dataclasses import dataclass


@dataclass
class PointCurveP521():
    A: int
    """Point value"""
    p: int = pow(2, 521) - 1
    """Modulus"""
    
    def __add__(self, other):
        return (self.A + other.A) % self.p
    def __mul__(self, other):
        return (self.A * other.A) % self.p
    def __sub__(self, other):
        return (self.A - other.A) % self.p
    def __truediv__(self, other):
        return self.A * pow(other.A, -1, self.p) % self.p
    def __mod__(self, other):
        pass
