-- How many tags does the official Python repository publish?
SELECT count(*) AS python_tags
FROM tags
WHERE repository = 'library/python';
