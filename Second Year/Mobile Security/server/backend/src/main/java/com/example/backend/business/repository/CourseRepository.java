package com.example.backend.business.repository;

import org.springframework.data.jpa.repository.JpaRepository;

import com.example.backend.core.domain.Course;

public interface CourseRepository extends JpaRepository<Course, Long> {

}
