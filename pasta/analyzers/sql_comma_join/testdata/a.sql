SELECT * FROM employee, salary; -- want "comma join in FROM"
SELECT id FROM a, b, c;          -- want "comma join in FROM"
SELECT * FROM employee e JOIN salary s ON e.id = s.id;
SELECT id FROM users;
