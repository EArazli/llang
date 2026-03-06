const mulDual = (l, r) => ({
  value: (l.value * r.value),
  derivative: ((l.value * r.derivative) + (l.derivative * r.value))
});

const sinDual = u => ({
  value: Math.sin(u.value),
  derivative: (Math.cos(u.value) * u.derivative)
});

export const timesSin = x => {
  const dx = { value: x, derivative: 1 };
  return mulDual(dx, sinDual(dx));
};
