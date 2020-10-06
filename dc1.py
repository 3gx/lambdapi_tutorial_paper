import mydataclasses as dc

@dc.dataclass
class S:
    x : int
    y : str

s = S(32, '32')
print(s, s.x, s.y)
